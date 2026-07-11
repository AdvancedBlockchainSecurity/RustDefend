use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ExprCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingSenderCheckDetector;

impl Detector for MissingSenderCheckDetector {
    fn id(&self) -> &'static str {
        "CW-003"
    }
    fn name(&self) -> &'static str {
        "missing-sender-check"
    }
    fn description(&self) -> &'static str {
        "Detects execute handler match arms that mutate storage without checking info.sender"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = SenderVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct SenderVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// True if a body string references an `info.sender` comparison (token or raw form).
fn body_has_sender_token(body: &str) -> bool {
    body.contains("info . sender") || body.contains("info.sender") || body.contains("sender")
}

/// True if the body is authorized economically via attached funds. CosmWasm
/// contracts routinely gate permissionless-looking handlers (deposit, bond,
/// crank) on `must_pay`/`one_coin`/`info.funds` instead of an `info.sender`
/// comparison — the caller pays for the state change, so no owner/admin check
/// is required and the missing sender comparison is not a defect.
fn body_has_funds_gate(body: &str) -> bool {
    body.contains("must_pay")
        || body.contains("one_coin")
        || body.contains("two_coins")
        || body.contains("info . funds")
        || body.contains("info.funds")
}

/// True if `attr` is a `#[test]`-style attribute (`#[test]`, `#[tokio::test]`,
/// `#[ink::test]`, `#[actix_rt::test]`, ...). The last path segment is `test`.
fn attr_is_test(attr: &Attribute) -> bool {
    attr.path()
        .segments
        .last()
        .map(|seg| seg.ident == "test")
        .unwrap_or(false)
}

/// True if the function carries a test attribute and is therefore not a real
/// contract entry point.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    attrs.iter().any(attr_is_test)
}

/// True if a module is gated behind `#[cfg(test)]` (so its contents are
/// compiled only for `cargo test`, never in the deployed wasm). We deliberately
/// exclude `#[cfg(not(test))]` so production-only code keeps being analyzed.
fn is_cfg_test_mod(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if !attr.path().is_ident("cfg") {
            return false;
        }
        let tokens = attr.meta.to_token_stream().to_string();
        tokens.contains("test") && !tokens.contains("not")
    })
}

/// Collects the names of free-function calls (last path segment) inside a
/// function body, e.g. `assert_owner(...)` -> "assert_owner".
struct CallNameCollector {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for CallNameCollector {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let syn::Expr::Path(p) = node.func.as_ref() {
            if let Some(seg) = p.path.segments.last() {
                let name = seg.ident.to_string();
                if !self.names.contains(&name) {
                    self.names.push(name);
                }
            }
        }
        syn::visit::visit_expr_call(self, node);
    }
}

impl<'a> SenderVisitor<'a> {
    /// Returns true if `func` delegates authorization to a helper that is
    /// resolvable in this file and whose body actually performs an
    /// `info.sender` check (e.g. `assert_owner(deps.as_ref(), &info)?`).
    ///
    /// This is a *resolved* check, not a name-based skip: we look up the
    /// callee's real body in the AST and only treat the caller as safe if that
    /// body contains a sender comparison. Helpers we cannot resolve in-file
    /// leave the finding intact.
    fn delegates_sender_check(&self, func: &ItemFn) -> bool {
        // Names of functions called from this execute body.
        let mut collector = CallNameCollector { names: Vec::new() };
        collector.visit_block(&func.block);
        if collector.names.is_empty() {
            return false;
        }

        // All function definitions available in this file.
        let mut fc = FunctionCollector {
            functions: Vec::new(),
        };
        fc.visit_file(&self.ctx.ast);

        for called in &collector.names {
            for def in &fc.functions {
                if def.sig.ident != called.as_str() {
                    continue;
                }
                // Don't let a function count as its own auth helper.
                if def.sig.ident == func.sig.ident {
                    continue;
                }
                let helper_body = fn_body_source(def);
                if body_has_sender_token(&helper_body) {
                    return true;
                }
            }
        }
        false
    }
}

impl<'ast, 'a> Visit<'ast> for SenderVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Skip modules compiled only under #[cfg(test)]: their contents are
        // unit tests (test setup routinely calls STATE.save directly against
        // mock storage) and are never reachable contract entry points.
        if is_cfg_test_mod(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions (#[test] / #[tokio::test] / #[ink::test] ...):
        // they are not contract entry points and have no auth semantics.
        if is_test_fn(&func.attrs) {
            return;
        }

        // Only analyze execute entry points
        if !fn_name.contains("execute") {
            return;
        }

        let body_src = fn_body_source(func);

        // Look for match on ExecuteMsg
        if !body_src.contains("ExecuteMsg") {
            return;
        }

        // Check each match arm conceptually
        // We'll look at the function body for save/update operations without sender checks
        let has_storage_mutation = body_src.contains(". save (")
            || body_src.contains(".save(")
            || body_src.contains(". update (")
            || body_src.contains(".update(")
            || body_src.contains(". remove (")
            || body_src.contains(".remove(");

        if !has_storage_mutation {
            return;
        }

        // The handler is considered authorized if:
        //  - it references info.sender directly, OR
        //  - it is gated economically by attached funds (must_pay/one_coin/...), OR
        //  - it delegates the sender check to a resolvable in-file helper.
        let has_sender_check = body_has_sender_token(&body_src)
            || body_has_funds_gate(&body_src)
            || self.delegates_sender_check(func);

        if !has_sender_check {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "CW-003".to_string(),
                name: "missing-sender-check".to_string(),
                severity: Severity::Critical,
                confidence: Confidence::Medium,
                message: format!(
                    "Execute handler '{}' mutates storage without checking info.sender",
                    fn_name
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Add `if info.sender != authorized_addr { return Err(...) }` before storage mutations".to_string(),
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
        MissingSenderCheckDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_sender() {
        let source = r#"
            fn execute_update_config(deps: DepsMut, info: MessageInfo, new_val: u64) -> StdResult<Response> {
                match msg {
                    ExecuteMsg::UpdateConfig { val } => {
                        CONFIG.save(deps.storage, &val)?;
                        Ok(Response::new())
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing sender check");
    }

    #[test]
    fn test_no_finding_with_sender() {
        let source = r#"
            fn execute_update_config(deps: DepsMut, info: MessageInfo, new_val: u64) -> StdResult<Response> {
                match msg {
                    ExecuteMsg::UpdateConfig { val } => {
                        if info.sender != owner {
                            return Err(StdError::generic_err("unauthorized"));
                        }
                        CONFIG.save(deps.storage, &val)?;
                        Ok(Response::new())
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with sender check");
    }

    // FP idx 0: inline #[cfg(test)] unit tests must not be flagged.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;
                use cosmwasm_std::testing::{mock_dependencies, mock_env, mock_info};

                #[test]
                fn execute_increment_works() {
                    let mut deps = mock_dependencies();
                    STATE.save(deps.as_mut().storage, &State { count: 0 }).unwrap();
                    let info = mock_info("anyone", &[]);
                    let res = execute(deps.as_mut(), mock_env(), info, ExecuteMsg::Increment {}).unwrap();
                    assert_eq!(0, res.messages.len());
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag test code inside #[cfg(test)] module"
        );
    }

    // FP idx 0 (variant): a bare #[test] fn (not wrapped in a module) is not a handler.
    #[test]
    fn test_no_finding_on_test_attr_fn() {
        let source = r#"
            #[test]
            fn execute_increment_works() {
                let mut deps = mock_dependencies();
                STATE.save(deps.as_mut().storage, &State { count: 0 }).unwrap();
                let res = execute(deps.as_mut(), mock_env(), info, ExecuteMsg::Increment {}).unwrap();
                assert_eq!(0, res.messages.len());
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag #[test] functions");
    }

    // FP idx 1: funds-gated (must_pay) handler is authorized economically.
    #[test]
    fn test_no_finding_with_funds_gate() {
        let source = r#"
            pub fn execute(deps: DepsMut, _env: Env, info: MessageInfo, msg: ExecuteMsg) -> Result<Response, ContractError> {
                match msg {
                    ExecuteMsg::Deposit {} => {
                        let amount = must_pay(&info, "uatom")?;
                        TOTAL.update(deps.storage, |t: Uint128| -> StdResult<_> { Ok(t + amount) })?;
                        Ok(Response::new())
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag handlers gated by attached funds (must_pay)"
        );
    }

    // FP idx 2: authorization delegated to an in-file helper that checks info.sender.
    #[test]
    fn test_no_finding_with_resolved_auth_helper() {
        let source = r#"
            fn assert_owner(deps: Deps, info: &MessageInfo) -> Result<(), ContractError> {
                let cfg = CONFIG.load(deps.storage)?;
                if info.sender != cfg.owner {
                    return Err(ContractError::Unauthorized {});
                }
                Ok(())
            }

            pub fn execute(deps: DepsMut, _env: Env, info: MessageInfo, msg: ExecuteMsg) -> Result<Response, ContractError> {
                match msg {
                    ExecuteMsg::UpdateConfig { cfg } => {
                        assert_owner(deps.as_ref(), &info)?;
                        CONFIG.save(deps.storage, &cfg)?;
                        Ok(Response::new())
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when auth is delegated to a resolvable helper that checks info.sender"
        );
    }

    // Soundness: an unrelated helper that does NOT check the sender must not
    // suppress the finding (no false negative from helper resolution).
    #[test]
    fn test_still_flags_when_helper_has_no_sender_check() {
        let source = r#"
            fn log_action(deps: Deps) -> Result<(), ContractError> {
                let _cfg = CONFIG.load(deps.storage)?;
                Ok(())
            }

            pub fn execute(deps: DepsMut, _env: Env, info: MessageInfo, msg: ExecuteMsg) -> Result<Response, ContractError> {
                match msg {
                    ExecuteMsg::UpdateConfig { cfg } => {
                        log_action(deps.as_ref())?;
                        CONFIG.save(deps.storage, &cfg)?;
                        Ok(Response::new())
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag when the called helper performs no sender check"
        );
    }
}
