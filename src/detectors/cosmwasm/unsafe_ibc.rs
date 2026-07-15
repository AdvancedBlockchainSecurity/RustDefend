use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ExprCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnsafeIbcDetector;

impl Detector for UnsafeIbcDetector {
    fn id(&self) -> &'static str {
        "CW-008"
    }
    fn name(&self) -> &'static str {
        "unsafe-ibc-entry-points"
    }
    fn description(&self) -> &'static str {
        "Detects IBC packet handlers without channel validation or proper timeout rollback"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Skip files that live under a `tests/` directory — any IBC handlers there
        // are test scaffolding (e.g. cw-multi-test counterparty mocks), never on-chain.
        if ctx.file_path.components().any(|c| c.as_os_str() == "tests") {
            return Vec::new();
        }

        // Check if file has ibc_channel_open (validates channels at connect time)
        let has_channel_open = ctx.source.contains("ibc_channel_open");

        // Build a same-file map of function name -> body source and name -> callees,
        // so a timeout handler that delegates its rollback to a helper (e.g. the
        // audited cw20-ics20 `on_packet_failure` pattern) can be resolved soundly.
        let mut collector = FunctionCollector {
            functions: Vec::new(),
        };
        collector.visit_file(&ctx.ast);

        let mut fn_bodies: HashMap<String, String> = HashMap::new();
        let mut fn_calls: HashMap<String, Vec<String>> = HashMap::new();
        for f in &collector.functions {
            let name = f.sig.ident.to_string();
            fn_bodies.insert(name.clone(), fn_body_source(f));
            let mut cc = CalleeCollector { calls: Vec::new() };
            cc.visit_item_fn(f);
            fn_calls.insert(name, cc.calls);
        }

        let mut findings = Vec::new();
        let mut visitor = IbcVisitor {
            findings: &mut findings,
            ctx,
            has_channel_open,
            fn_bodies: &fn_bodies,
            fn_calls: &fn_calls,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const IBC_HANDLER_FUNCTIONS: &[&str] = &[
    "ibc_packet_receive",
    "ibc_packet_ack",
    "ibc_source_callback",
    "ibc_destination_callback",
];

const IBC_TIMEOUT_FUNCTIONS: &[&str] = &["ibc_packet_timeout"];

const CHANNEL_SAFE_PATTERNS: &[&str] = &[
    "channel_id",
    "dest . channel_id",
    "src . channel_id",
    "ALLOWED_CHANNEL",
    "IBC_CHANNEL",
];

const TIMEOUT_SAFE_PATTERNS: &[&str] = &[
    "refund",
    "rollback",
    "revert",
    "restore",
    "undo",
    "return_funds",
];

const TIMEOUT_STORAGE_PATTERNS: &[&str] = &[".save(", ".update(", ".remove("];

/// Message-emitting patterns. A timeout handler (or a helper it delegates to)
/// that sends a message is refunding/returning escrowed value — i.e. it performs
/// the rollback the detector demands, just via a bank/IBC/wasm message.
const SEND_MESSAGE_PATTERNS: &[&str] = &[
    "add_message",
    "add_messages",
    "add_submessage",
    "add_submessages",
    "BankMsg",
    "IbcMsg",
    "WasmMsg",
    "send_amount",
    "send_tokens",
];

/// Panicking-stub macros (token-stream spelling). A small handler that only
/// panics processes no packet data and holds no revertible state.
const PANIC_STUB_PATTERNS: &[&str] = &["unimplemented !", "unreachable !", "todo !", "panic !"];

struct IbcVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    has_channel_open: bool,
    fn_bodies: &'a HashMap<String, String>,
    fn_calls: &'a HashMap<String, Vec<String>>,
}

impl<'a> IbcVisitor<'a> {
    /// Returns true if the timeout handler `name`, or a same-file function it
    /// transitively calls (up to two levels deep), performs a rollback: restores
    /// state (TIMEOUT_SAFE_PATTERNS), mutates storage (TIMEOUT_STORAGE_PATTERNS),
    /// or emits a message returning escrowed funds (SEND_MESSAGE_PATTERNS).
    fn timeout_chain_is_safe(&self, name: &str) -> bool {
        let mut visited: Vec<String> = Vec::new();
        self.chain_safe_rec(name, 0, &mut visited)
    }

    fn chain_safe_rec(&self, name: &str, depth: usize, visited: &mut Vec<String>) -> bool {
        if depth > 2 {
            return false;
        }
        let callees = match self.fn_calls.get(name) {
            Some(c) => c,
            None => return false,
        };
        for callee in callees {
            if visited.contains(callee) {
                continue;
            }
            visited.push(callee.clone());
            if let Some(body) = self.fn_bodies.get(callee) {
                if TIMEOUT_SAFE_PATTERNS.iter().any(|p| body.contains(p))
                    || TIMEOUT_STORAGE_PATTERNS.iter().any(|p| body.contains(p))
                    || SEND_MESSAGE_PATTERNS.iter().any(|p| body.contains(p))
                {
                    return true;
                }
                if self.chain_safe_rec(callee, depth + 1, visited) {
                    return true;
                }
            }
        }
        false
    }
}

impl<'ast, 'a> Visit<'ast> for IbcVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Skip `#[cfg(test)]` modules entirely: mock IBC handlers registered with
        // cw-multi-test keep the exact entry-point names but never run on-chain.
        if attrs_have_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions
        if fn_name.starts_with("test_")
            || fn_name.ends_with("_test")
            || has_attribute(&func.attrs, "test")
        {
            return;
        }

        let body_src = fn_body_source(func);

        // Check if handler only returns error (intentional rejection)
        let body_trimmed = body_src.trim();
        if body_trimmed.contains("Err (") || body_trimmed.contains("StdError ::") {
            // Simple heuristic: if function body is small and returns error
            let non_whitespace: String = body_trimmed
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();
            if non_whitespace.len() < 200
                && (non_whitespace.contains("Err(")
                    || non_whitespace.contains("IbcReceiveResponse::new()"))
            {
                // Very small function that just returns error or empty response
                if !non_whitespace.contains(".save(")
                    && !non_whitespace.contains(".update(")
                    && !non_whitespace.contains(".remove(")
                {
                    return;
                }
            }
        }

        // Unreachable / panicking stub: a receive-only contract must still export
        // ibc_packet_ack / ibc_packet_timeout, and the idiomatic body is
        // `unimplemented!()` / `unreachable!()` / `panic!()` / `todo!()`. Such a
        // stub processes no packet data and holds no revertible state, so there is
        // nothing to validate or roll back. Reuse the same small-body + no-storage
        // guards so a large handler that merely panics on one path is still analyzed.
        {
            let non_whitespace: String = body_trimmed
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();
            if non_whitespace.len() < 200
                && !non_whitespace.contains(".save(")
                && !non_whitespace.contains(".update(")
                && !non_whitespace.contains(".remove(")
                && PANIC_STUB_PATTERNS.iter().any(|p| body_src.contains(p))
            {
                return;
            }
        }

        // Check IBC receive/ack/callback handlers
        if IBC_HANDLER_FUNCTIONS.contains(&fn_name.as_str()) {
            // Skip if ibc_channel_open validates channels in same file
            if self.has_channel_open {
                return;
            }

            let has_channel_check = CHANNEL_SAFE_PATTERNS.iter().any(|p| body_src.contains(p));

            if !has_channel_check {
                let line = span_to_line(&func.sig.ident.span());
                self.findings.push(Finding {
                    detector_id: "CW-008".to_string(),
                    name: "unsafe-ibc-entry-points".to_string(),
                    severity: Severity::High,
                    confidence: Confidence::Medium,
                    message: format!(
                        "IBC handler '{}' does not validate the source/destination channel",
                        fn_name
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&func.sig.ident.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Validate channel_id against an allowed list, or implement ibc_channel_open to filter channels at connection time".to_string(),
                    chain: Chain::CosmWasm,
                });
            }
        }

        // Check IBC timeout handlers
        if IBC_TIMEOUT_FUNCTIONS.contains(&fn_name.as_str()) {
            let has_rollback = TIMEOUT_SAFE_PATTERNS.iter().any(|p| body_src.contains(p));
            let has_storage_mutation = TIMEOUT_STORAGE_PATTERNS
                .iter()
                .any(|p| body_src.contains(p));
            // The rollback may be delegated to a same-file helper (audited
            // cw20-ics20 `on_packet_failure` pattern): resolve the call chain.
            let delegated_rollback =
                !has_rollback && !has_storage_mutation && self.timeout_chain_is_safe(&fn_name);

            if !has_rollback && !has_storage_mutation && !delegated_rollback {
                let line = span_to_line(&func.sig.ident.span());
                self.findings.push(Finding {
                    detector_id: "CW-008".to_string(),
                    name: "unsafe-ibc-entry-points".to_string(),
                    severity: Severity::High,
                    confidence: Confidence::Medium,
                    message: format!(
                        "IBC timeout handler '{}' does not perform rollback or state cleanup",
                        fn_name
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&func.sig.ident.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Implement rollback logic in timeout handlers to refund/revert state when IBC packets time out".to_string(),
                    chain: Chain::CosmWasm,
                });
            }
        }
    }
}

/// Collects the names of plain function calls (`ExprCall` with a path callee)
/// made within a function, used to resolve same-file rollback helpers.
struct CalleeCollector {
    calls: Vec<String>,
}

impl<'ast> Visit<'ast> for CalleeCollector {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let syn::Expr::Path(p) = node.func.as_ref() {
            if let Some(seg) = p.path.segments.last() {
                let name = seg.ident.to_string();
                if !self.calls.contains(&name) {
                    self.calls.push(name);
                }
            }
        }
        syn::visit::visit_expr_call(self, node);
    }
}

/// True if the attribute list carries a `#[cfg(test)]` (including forms like
/// `#[cfg(all(test, ...))]`).
fn attrs_have_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if let Some(ident) = attr.path().get_ident() {
            if ident == "cfg" {
                let tokens = attr.meta.to_token_stream().to_string().replace(' ', "");
                return tokens == "cfg(test)"
                    || tokens.contains("(test)")
                    || tokens.contains("(test,")
                    || tokens.contains(",test,")
                    || tokens.contains(",test)");
            }
        }
        false
    })
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
        UnsafeIbcDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_ibc_receive_without_channel_check() {
        let source = r#"
            fn ibc_packet_receive(deps: DepsMut, env: Env, msg: IbcPacketReceiveMsg) -> StdResult<IbcReceiveResponse> {
                let packet = msg.packet;
                let data: TransferMsg = from_binary(&packet.data)?;
                execute_transfer(deps, data.recipient, data.amount)?;
                Ok(IbcReceiveResponse::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect IBC receive without channel validation"
        );
        assert_eq!(findings[0].detector_id, "CW-008");
    }

    #[test]
    fn test_no_finding_with_channel_validation() {
        let source = r#"
            fn ibc_packet_receive(deps: DepsMut, env: Env, msg: IbcPacketReceiveMsg) -> StdResult<IbcReceiveResponse> {
                let packet = msg.packet;
                let channel = packet.dest.channel_id;
                if channel != IBC_CHANNEL.load(deps.storage)? {
                    return Err(StdError::generic_err("unauthorized channel"));
                }
                let data: TransferMsg = from_binary(&packet.data)?;
                execute_transfer(deps, data.recipient, data.amount)?;
                Ok(IbcReceiveResponse::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when channel validation is present"
        );
    }

    #[test]
    fn test_detects_empty_timeout_handler() {
        let source = r#"
            fn ibc_packet_timeout(deps: DepsMut, env: Env, msg: IbcPacketTimeoutMsg) -> StdResult<IbcBasicResponse> {
                Ok(IbcBasicResponse::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect empty timeout handler");
    }

    #[test]
    fn test_no_finding_timeout_with_rollback() {
        let source = r#"
            fn ibc_packet_timeout(deps: DepsMut, env: Env, msg: IbcPacketTimeoutMsg) -> StdResult<IbcBasicResponse> {
                let packet = msg.packet;
                let data: TransferMsg = from_binary(&packet.data)?;
                refund(deps, data.sender, data.amount)?;
                Ok(IbcBasicResponse::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag timeout handler with rollback"
        );
    }

    #[test]
    fn test_no_finding_with_channel_open_in_file() {
        let source = r#"
            fn ibc_channel_open(deps: DepsMut, env: Env, msg: IbcChannelOpenMsg) -> StdResult<()> {
                validate_channel(msg.channel())?;
                Ok(())
            }

            fn ibc_packet_receive(deps: DepsMut, env: Env, msg: IbcPacketReceiveMsg) -> StdResult<IbcReceiveResponse> {
                let packet = msg.packet;
                let data: TransferMsg = from_binary(&packet.data)?;
                execute_transfer(deps, data.recipient, data.amount)?;
                Ok(IbcReceiveResponse::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when ibc_channel_open validates channels"
        );
    }

    // ---- FP-elimination regression tests ----

    // FP idx 1: timeout handler delegates the rollback to a same-file helper
    // (verbatim cw20-ics20 `on_packet_failure` pattern). The helper restores the
    // channel balance and sends the escrowed funds back to the sender.
    #[test]
    fn test_no_finding_timeout_delegating_to_failure_helper() {
        let source = r#"
            pub fn ibc_packet_timeout(
                deps: DepsMut,
                _env: Env,
                msg: IbcPacketTimeoutMsg,
            ) -> Result<IbcBasicResponse, ContractError> {
                let packet = msg.packet;
                on_packet_failure(deps, packet, "timeout")
            }

            fn on_packet_failure(
                deps: DepsMut,
                packet: IbcPacket,
                err: &str,
            ) -> Result<IbcBasicResponse, ContractError> {
                let msg: Ics20Packet = from_binary(&packet.data)?;
                reduce_channel_balance(deps.storage, &packet.src.channel_id, &msg.denom, msg.amount)?;
                let to_send = Amount::from_parts(msg.denom, msg.amount);
                Ok(IbcBasicResponse::new().add_message(send_amount(to_send, msg.sender)))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a timeout handler whose helper restores state and refunds"
        );
    }

    // FP idx 2: unreachable panicking stub for ibc_packet_ack in a receive-only
    // contract. Nothing is processed and nothing is held, so no finding.
    #[test]
    fn test_no_finding_panic_stub_ack_handler() {
        let source = r#"
            pub fn ibc_packet_ack(
                _deps: DepsMut,
                _env: Env,
                _msg: IbcPacketAckMsg,
            ) -> StdResult<IbcBasicResponse> {
                // This contract never sends packets, so an ack can never arrive.
                unimplemented!();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag an unreachable panicking ack stub"
        );
    }

    // FP idx 2 (timeout variant): unreachable panicking timeout stub.
    #[test]
    fn test_no_finding_panic_stub_timeout_handler() {
        let source = r#"
            pub fn ibc_packet_timeout(
                _deps: DepsMut,
                _env: Env,
                _msg: IbcPacketTimeoutMsg,
            ) -> StdResult<IbcBasicResponse> {
                unreachable!();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag an unreachable panicking timeout stub"
        );
    }

    // FP idx 4: mock IBC handler inside a #[cfg(test)] module (cw-multi-test
    // counterparty scaffolding). Never compiled into release wasm.
    #[test]
    fn test_no_finding_mock_handler_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod multitest {
                use super::*;
                fn ibc_packet_receive(
                    deps: DepsMut,
                    _env: Env,
                    _msg: IbcPacketReceiveMsg,
                ) -> StdResult<IbcReceiveResponse> {
                    Ok(IbcReceiveResponse::new().set_ack(b"{}"))
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag mock IBC handlers in #[cfg(test)] modules"
        );
    }

    // Guard soundness: a real vulnerable receive handler nested in a NON-test
    // module must still fire (proves the cfg(test) skip is not a blanket module skip).
    #[test]
    fn test_still_flags_handler_in_plain_module() {
        let source = r#"
            mod ibc {
                fn ibc_packet_receive(
                    deps: DepsMut,
                    env: Env,
                    msg: IbcPacketReceiveMsg,
                ) -> StdResult<IbcReceiveResponse> {
                    let packet = msg.packet;
                    let data: TransferMsg = from_binary(&packet.data)?;
                    execute_transfer(deps, data.recipient, data.amount)?;
                    Ok(IbcReceiveResponse::new())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag an unvalidated handler in a non-test module"
        );
    }
}
