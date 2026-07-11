use quote::ToTokens;
use syn::visit::Visit;
use syn::{Expr, ItemFn, Stmt};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct ReentrancyDetector;

impl Detector for ReentrancyDetector {
    fn id(&self) -> &'static str {
        "CW-002"
    }
    fn name(&self) -> &'static str {
        "cosmwasm-reentrancy"
    }
    fn description(&self) -> &'static str {
        "Detects storage writes followed by add_message/add_submessage (CEI violation) - informational: CosmWasm is non-reentrant by design"
    }
    fn severity(&self) -> Severity {
        Severity::Low
    }
    fn confidence(&self) -> Confidence {
        Confidence::Low
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = ReentrancyVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct ReentrancyVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// Token-stream text of a leaf statement/expression that performs a storage write.
fn is_save_tokens(s: &str) -> bool {
    s.contains(".save(") || s.contains(". save (")
}

/// Token-stream text of a leaf statement/expression that dispatches an external message.
fn is_dispatch_tokens(s: &str) -> bool {
    s.contains("add_message") || s.contains("add_submessage") || s.contains("WasmMsg :: Execute")
}

/// The "core" expression carried by a statement (the init of a `let`, or the
/// expression of an expression-statement). Used to find control-flow so we can
/// walk each branch independently instead of stringifying the whole statement.
fn stmt_core_expr(stmt: &Stmt) -> Option<&Expr> {
    match stmt {
        Stmt::Expr(e, _) => Some(e),
        Stmt::Local(local) => local.init.as_ref().map(|init| init.expr.as_ref()),
        _ => None,
    }
}

/// Peel transparent wrappers (`?`, `return`, parentheses) so a control-flow
/// expression underneath is reached.
fn peel_expr(expr: &Expr) -> &Expr {
    match expr {
        Expr::Try(t) => peel_expr(&t.expr),
        Expr::Paren(p) => peel_expr(&p.expr),
        Expr::Return(r) => match &r.expr {
            Some(e) => peel_expr(e),
            None => expr,
        },
        _ => expr,
    }
}

/// Path-sensitive scan of a statement sequence.
///
/// Returns `(found, seen_save_out)` where `found` is true when some execution
/// path performs a storage write and then, later on that same path, dispatches
/// an external message (the CEI-ordering pattern this detector reports).
/// `seen_save_out` reports whether a save is guaranteed on every path through
/// the sequence (for sequential composition with later statements).
///
/// Crucially, `match`/`if` branches are explored independently: a save in one
/// arm and a dispatch in a mutually-exclusive arm never combine into a finding.
fn scan_stmts(stmts: &[Stmt], mut seen_save: bool) -> (bool, bool) {
    for stmt in stmts {
        if let Some(expr) = stmt_core_expr(stmt) {
            let core = peel_expr(expr);
            if matches!(core, Expr::Match(_) | Expr::If(_) | Expr::Block(_)) {
                let (found, ss) = scan_expr(core, seen_save);
                if found {
                    return (true, true);
                }
                seen_save = ss;
                continue;
            }
        }

        // Leaf statement: classify by its token stream.
        let s = stmt.to_token_stream().to_string();
        if is_save_tokens(&s) {
            seen_save = true;
        }
        if seen_save && is_dispatch_tokens(&s) {
            return (true, true);
        }
    }
    (false, seen_save)
}

/// Path-sensitive scan of a single expression (used for branch bodies).
fn scan_expr(expr: &Expr, seen_save: bool) -> (bool, bool) {
    match expr {
        Expr::Block(b) => scan_stmts(&b.block.stmts, seen_save),
        Expr::Match(m) => {
            let mut all_arms_save = !m.arms.is_empty();
            for arm in &m.arms {
                let (found, ss) = scan_expr(peel_expr(&arm.body), seen_save);
                if found {
                    return (true, true);
                }
                all_arms_save &= ss;
            }
            (false, seen_save || all_arms_save)
        }
        Expr::If(i) => {
            let (f1, s1) = scan_stmts(&i.then_branch.stmts, seen_save);
            if f1 {
                return (true, true);
            }
            match &i.else_branch {
                Some((_, else_expr)) => {
                    let (f2, s2) = scan_expr(peel_expr(else_expr), seen_save);
                    if f2 {
                        return (true, true);
                    }
                    // Save is guaranteed after the `if` only when both branches save.
                    (false, seen_save || (s1 && s2))
                }
                // No `else`: the then-branch may be skipped, so no new guarantee.
                None => (false, seen_save),
            }
        }
        other => {
            let s = other.to_token_stream().to_string();
            let mut ss = seen_save;
            if is_save_tokens(&s) {
                ss = true;
            }
            if ss && is_dispatch_tokens(&s) {
                return (true, true);
            }
            (false, ss)
        }
    }
}

impl<'ast, 'a> Visit<'ast> for ReentrancyVisitor<'a> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions
        if fn_name.contains("test")
            || fn_name.contains("_works")
            || fn_name.contains("_mock")
            || fn_name.contains("_should")
            || has_attribute(&func.attrs, "test")
        {
            return;
        }

        let body_src = fn_body_source(func);

        // Must contain both storage save and message dispatch
        if !body_src.contains(".save(") && !body_src.contains(". save (") {
            return;
        }

        let has_message = body_src.contains("add_message")
            || body_src.contains("add_submessage")
            || body_src.contains("WasmMsg");

        if !has_message {
            return;
        }

        // CosmWasm is non-reentrant by design. The only class where an external
        // message can re-enter mid-flow is the IBC packet/hook path
        // (CWA-2024-007 reentrancy via ibc-hooks). Restrict the detector to
        // genuine IBC entry points, identified by:
        //   - an `ibc_`-prefixed function name (ibc_packet_receive,
        //     ibc_channel_open, ibc_channel_connect, ...), or
        //   - construction/use of an IBC type in the body (case-sensitive so a
        //     lowercase "ibc/<hash>" denom string literal does not qualify).
        //
        // Deliberately NOT keyed on `SubMsg`/`ReplyOn`/`reply`: the
        // instantiate-reply/factory pattern (save config, then dispatch a
        // SubMsg to instantiate a child, then a reply handler that persists the
        // new address and configures it) executes the submessage only after the
        // function returns with its storage writes committed. That is the
        // actor-model, non-reentrant, CEI-correct idiom, not a vulnerability.
        let is_ibc_relevant = fn_name.starts_with("ibc_")
            || body_src.contains("IbcMsg")
            || body_src.contains("IbcPacket")
            || body_src.contains("IbcChannel")
            || body_src.contains("IbcTimeout");

        if !is_ibc_relevant {
            return;
        }

        // Path-sensitive ordering check: report only when a storage write is
        // followed by a message dispatch on the SAME execution path. Saves and
        // dispatches sitting in mutually exclusive match arms / if branches are
        // not a save-then-dispatch sequence and must not be flagged.
        let (found, _) = scan_stmts(&func.block.stmts, false);
        if found {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "CW-002".to_string(),
                name: "cosmwasm-reentrancy".to_string(),
                severity: Severity::Low,
                confidence: Confidence::Low,
                message: format!(
                    "Function '{}' writes to storage before dispatching external message",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "CosmWasm's actor model prevents reentrancy by design. This is informational for code organization. Consider CEI pattern if using IBC hooks".to_string(),
                chain: Chain::CosmWasm,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_detector(source: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let ctx = ScanContext::new(
            std::path::PathBuf::from("test.rs"),
            source.to_string(),
            ast,
            Chain::CosmWasm,
            std::collections::HashMap::new(),
        );
        ReentrancyDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_save_before_message_in_ibc() {
        let source = r#"
            fn ibc_packet_receive(deps: DepsMut, msg: IbcPacketReceiveMsg) -> StdResult<Response> {
                STATE.save(deps.storage, &new_state)?;
                Ok(Response::new().add_message(WasmMsg::Execute { .. }))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect save before add_message in IBC handler"
        );
    }

    #[test]
    fn test_no_finding_non_ibc_handler() {
        let source = r#"
            fn execute_transfer(deps: DepsMut, info: MessageInfo) -> StdResult<Response> {
                STATE.save(deps.storage, &new_state)?;
                Ok(Response::new().add_message(WasmMsg::Execute { .. }))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag non-IBC handler (CosmWasm is non-reentrant by design)"
        );
    }

    // FP idx 0: canonical factory pattern (save config, then dispatch a SubMsg
    // to instantiate a child contract). No IBC surface; the SubMsg runs only
    // after this function returns with state committed.
    #[test]
    fn test_no_finding_submsg_factory_pattern() {
        let source = r#"
            pub fn execute_create_pool(deps: DepsMut, env: Env, info: MessageInfo) -> StdResult<Response> {
                CONFIG.save(deps.storage, &Config { owner: info.sender.clone() })?;
                let sub = SubMsg::reply_on_success(
                    WasmMsg::Instantiate {
                        admin: None,
                        code_id: 42,
                        msg: to_json_binary(&TokenInit {})?,
                        funds: vec![],
                        label: "lp-token".into(),
                    },
                    INSTANTIATE_REPLY_ID,
                );
                Ok(Response::new().add_submessage(sub))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag the instantiate-reply/factory SubMsg pattern (no IBC surface)"
        );
    }

    // FP idx 1: a plain execute handler paying out a native token whose denom
    // is an IBC-transferred asset ("ibc/<hash>"). The lowercase "ibc" is only a
    // denom string literal, not an IBC entry point.
    #[test]
    fn test_no_finding_ibc_denom_string_literal() {
        let source = r#"
            pub fn execute_claim(deps: DepsMut, env: Env, info: MessageInfo) -> StdResult<Response> {
                let mut acct = ACCOUNTS.load(deps.storage, &info.sender)?;
                let amount = acct.pending;
                acct.pending = Uint128::zero();
                ACCOUNTS.save(deps.storage, &info.sender, &acct)?;
                let pay = BankMsg::Send {
                    to_address: info.sender.to_string(),
                    amount: vec![Coin::new(amount.u128(), "ibc/27394FB092D2ECCD56123C74F36E4C1F926001CEADA9CA97EA622B25F41E5EB2")],
                };
                Ok(Response::new().add_message(pay))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a normal execute handler whose payout denom is an ibc/<hash> literal"
        );
    }

    // FP idx 2: standard reply handler after reply_on_success instantiation:
    // persist the child address, then send it a configuration message. A reply
    // handler is not an IBC hook path.
    #[test]
    fn test_no_finding_standard_reply_handler() {
        let source = r#"
            pub fn reply(deps: DepsMut, _env: Env, msg: Reply) -> StdResult<Response> {
                let res = parse_instantiate_response_data(&msg.result.unwrap().data.unwrap())?;
                let token_addr = deps.api.addr_validate(&res.contract_address)?;
                LP_TOKEN.save(deps.storage, &token_addr)?;
                Ok(Response::new().add_message(WasmMsg::Execute {
                    contract_addr: token_addr.to_string(),
                    msg: to_json_binary(&Cw20ExecuteMsg::UpdateMinter { new_minter: None })?,
                    funds: vec![],
                }))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a standard reply handler (not an IBC hook path)"
        );
    }

    // FP idx 3: save and add_message live in mutually exclusive match arms of an
    // IBC packet receive handler. No single path does save-then-dispatch.
    #[test]
    fn test_no_finding_save_and_dispatch_in_exclusive_match_arms() {
        let source = r#"
            pub fn ibc_packet_receive(deps: DepsMut, _env: Env, msg: IbcPacketReceiveMsg) -> StdResult<IbcReceiveResponse> {
                let packet: PacketMsg = from_json(&msg.packet.data)?;
                match packet {
                    PacketMsg::UpdateState { value } => {
                        STATE.save(deps.storage, &value)?;
                        Ok(IbcReceiveResponse::new(ack_success()))
                    }
                    PacketMsg::Forward { msg } => {
                        Ok(IbcReceiveResponse::new(ack_success()).add_message(msg))
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag save and dispatch that occur in mutually exclusive match arms"
        );
    }

    // Guard against regression: a genuine save-then-dispatch inside one IBC
    // match arm must still fire.
    #[test]
    fn test_detects_save_then_dispatch_within_single_ibc_arm() {
        let source = r#"
            pub fn ibc_packet_receive(deps: DepsMut, _env: Env, msg: IbcPacketReceiveMsg) -> StdResult<IbcReceiveResponse> {
                let packet: PacketMsg = from_json(&msg.packet.data)?;
                match packet {
                    PacketMsg::UpdateState { value } => {
                        STATE.save(deps.storage, &value)?;
                        Ok(IbcReceiveResponse::new(ack_success()).add_message(WasmMsg::Execute { .. }))
                    }
                    PacketMsg::Noop {} => {
                        Ok(IbcReceiveResponse::new(ack_success()))
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still detect save-then-dispatch within a single IBC match arm"
        );
    }
}
