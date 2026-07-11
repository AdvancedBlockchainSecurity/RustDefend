use std::collections::HashMap;
use std::path::Path;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, ExprCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingReplyIdDetector;

impl Detector for MissingReplyIdDetector {
    fn id(&self) -> &'static str {
        "CW-011"
    }
    fn name(&self) -> &'static str {
        "missing-reply-id-validation"
    }
    fn description(&self) -> &'static str {
        "Detects reply handler not matching on msg.id, processing all submessage replies identically"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = ReplyVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const REPLY_ID_PATTERNS: &[&str] = &[
    "msg . id",
    "msg.id",
    "reply . id",
    "reply.id",
    "REPLY_ID",
    "INSTANTIATE_REPLY",
    "EXECUTE_REPLY",
    "reply_id",
    "SubMsgResult",
    "match msg",
    "match reply",
];

/// Returns true if a reply-handler body demonstrably discriminates on the reply id.
///
/// This covers the original substring patterns plus the struct-destructuring idiom
/// (`let Reply { id, .. } = msg; match id { .. }`), which produces a token stream
/// matching none of the flat patterns above. The destructuring branch is deliberately
/// narrow: it only counts as an id check when a `Reply { .. }` pattern is present AND
/// the body actually matches/compares on `id`, so a handler that binds `id` (or other
/// fields) and never discriminates is still flagged.
fn body_has_id_check(body_src: &str) -> bool {
    if REPLY_ID_PATTERNS.iter().any(|p| body_src.contains(p)) {
        return true;
    }
    has_destructured_id_check(body_src)
}

/// Recognizes `let Reply { id, .. } = msg;` followed by discrimination on `id`.
fn has_destructured_id_check(body_src: &str) -> bool {
    // `func.block.to_token_stream()` renders struct patterns as `Reply { id , .. }`.
    let destructures_reply = body_src.contains("Reply {");
    if !destructures_reply {
        return false;
    }
    body_src.contains("match id")
        || body_src.contains("match ( id")
        || body_src.contains("id ==")
        || body_src.contains("id !=")
}

/// True if the file being scanned is test scaffolding rather than a shipped contract.
///
/// Deliberately conservative so that in-crate helper `test.rs` fixtures used by the
/// detector's own unit tests (path `test.rs`) are NOT treated as test files — only a
/// `tests/` integration-test directory component or a `_test.rs` / `_tests.rs` filename.
fn is_test_file(path: &Path) -> bool {
    if path
        .components()
        .any(|c| c.as_os_str() == "tests" || c.as_os_str() == "test")
    {
        return true;
    }
    if let Some(name) = path.file_name().and_then(|s| s.to_str()) {
        if name.ends_with("_test.rs") || name.ends_with("_tests.rs") {
            return true;
        }
    }
    false
}

/// True for `#[cfg(test)]` (exactly), not for `#[cfg(feature = "test-utils")]` etc.
fn attr_is_cfg_test(attr: &Attribute) -> bool {
    if attr.path().is_ident("cfg") {
        let toks = attr.meta.to_token_stream().to_string();
        let normalized: String = toks.chars().filter(|c| !c.is_whitespace()).collect();
        return normalized == "cfg(test)";
    }
    false
}

/// Extract the identifier of the parameter typed `Reply` (e.g. `msg`).
fn reply_param_ident(func: &ItemFn) -> Option<String> {
    for input in &func.sig.inputs {
        if let syn::FnArg::Typed(pat_type) = input {
            let ty = pat_type.ty.to_token_stream().to_string();
            if ty.contains("Reply") {
                if let syn::Pat::Ident(pi) = &*pat_type.pat {
                    return Some(pi.ident.to_string());
                }
            }
        }
    }
    None
}

/// True if `expr` is exactly the identifier `name`.
fn expr_is_ident(expr: &Expr, name: &str) -> bool {
    if let Expr::Path(p) = expr {
        return p.path.get_ident().map(|i| i == name).unwrap_or(false);
    }
    false
}

/// Collect the names of functions that the reply body forwards the Reply param into.
/// Only calls whose argument list includes the reply-param ident are considered, so we
/// follow genuine delegation (`handle_reply(deps, env, msg)`) and not unrelated helpers.
struct ForwardCollector<'p> {
    param: &'p str,
    callees: Vec<String>,
}

impl<'ast, 'p> Visit<'ast> for ForwardCollector<'p> {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        let forwards = node.args.iter().any(|a| expr_is_ident(a, self.param));
        if forwards {
            if let Expr::Path(p) = node.func.as_ref() {
                if let Some(seg) = p.path.segments.last() {
                    let name = seg.ident.to_string();
                    if !self.callees.contains(&name) {
                        self.callees.push(name);
                    }
                }
            }
        }
        syn::visit::visit_expr_call(self, node);
    }
}

/// Build a map of `fn name -> token-stream body` for every function item in the file.
fn collect_fn_bodies(ast: &syn::File) -> HashMap<String, String> {
    let mut fc = FunctionCollector {
        functions: Vec::new(),
    };
    fc.visit_file(ast);
    fc.functions
        .into_iter()
        .map(|f| {
            (
                f.sig.ident.to_string(),
                f.block.to_token_stream().to_string(),
            )
        })
        .collect()
}

/// Sound (same-file only) resolution of the "thin entry point delegates to a handler
/// that does the id match" pattern. Suppresses the finding only when a forwarded callee
/// is resolvable in THIS file and its body actually contains an id check. Cross-file
/// callees are not resolvable here (the crate call graph records no id-discrimination
/// signal), so those remain flagged — no false negatives are introduced.
fn delegates_id_check(func: &ItemFn, ast: &syn::File) -> bool {
    let param = match reply_param_ident(func) {
        Some(p) => p,
        None => return false,
    };
    let mut collector = ForwardCollector {
        param: &param,
        callees: Vec::new(),
    };
    collector.visit_block(&func.block);
    if collector.callees.is_empty() {
        return false;
    }
    let bodies = collect_fn_bodies(ast);
    collector
        .callees
        .iter()
        .filter_map(|name| bodies.get(name))
        .any(|body| body_has_id_check(body))
}

struct ReplyVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for ReplyVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Do not descend into `#[cfg(test)]` modules: helper fns there (e.g. mock
        // reply handlers) never ship on chain and must not be flagged.
        if node.attrs.iter().any(attr_is_cfg_test) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Only check reply entry points
        if fn_name != "reply" {
            return;
        }

        // Skip test functions
        if has_attribute(&func.attrs, "test") {
            return;
        }

        // Skip test scaffolding files (integration tests, `*_test.rs`): mock reply
        // handlers wired into cw-multi-test are stubs, not on-chain code.
        if is_test_file(&self.ctx.file_path) {
            return;
        }

        let body_src = fn_body_source(func);

        // Skip trivial implementations
        let body_trimmed: String = body_src.chars().filter(|c| !c.is_whitespace()).collect();
        if body_trimmed.len() < 50 {
            return;
        }

        if body_has_id_check(&body_src) {
            return;
        }

        // The handler itself has no id check, but a thin entry point may forward the
        // Reply to a same-file handler that does the discrimination. Only suppress when
        // that callee is resolvable here and actually contains an id check.
        if delegates_id_check(func, &self.ctx.ast) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "CW-011".to_string(),
            name: "missing-reply-id-validation".to_string(),
            severity: Severity::Medium,
            confidence: Confidence::Medium,
            message: format!(
                "Reply handler '{}' does not match on msg.id — all submessage replies processed identically",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Match on msg.id to distinguish between different submessage replies (e.g., match msg.id { INSTANTIATE_REPLY_ID => ..., _ => ... })".to_string(),
            chain: Chain::CosmWasm,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_detector(source: &str) -> Vec<Finding> {
        run_detector_at(source, "test.rs")
    }

    fn run_detector_at(source: &str, path: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let ctx = ScanContext::new(
            std::path::PathBuf::from(path),
            source.to_string(),
            ast,
            Chain::CosmWasm,
            std::collections::HashMap::new(),
        );
        MissingReplyIdDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_reply_without_id_check() {
        let source = r#"
            fn reply(deps: DepsMut, env: Env, msg: Reply) -> StdResult<Response> {
                let result = msg.result.into_result().map_err(StdError::generic_err)?;
                let event = result.events.iter().find(|e| e.ty == "instantiate").unwrap();
                let addr = &event.attributes[0].value;
                CHILD_CONTRACT.save(deps.storage, &deps.api.addr_validate(addr)?)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect reply without msg.id check"
        );
        assert_eq!(findings[0].detector_id, "CW-011");
    }

    #[test]
    fn test_no_finding_with_id_match() {
        let source = r#"
            fn reply(deps: DepsMut, env: Env, msg: Reply) -> StdResult<Response> {
                match msg.id {
                    INSTANTIATE_REPLY => handle_instantiate_reply(deps, msg),
                    EXECUTE_REPLY => handle_execute_reply(deps, msg),
                    id => Err(StdError::generic_err(format!("unknown reply id: {}", id))),
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when msg.id is matched"
        );
    }

    #[test]
    fn test_no_finding_with_reply_id_constant() {
        let source = r#"
            fn reply(deps: DepsMut, env: Env, msg: Reply) -> StdResult<Response> {
                if msg.id != REPLY_ID {
                    return Err(StdError::generic_err("unexpected reply"));
                }
                let result = msg.result.into_result().map_err(StdError::generic_err)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when reply.id is checked"
        );
    }

    // --- FP idx 2: `let Reply { id, .. } = msg; match id { .. }` destructuring idiom ---
    #[test]
    fn test_no_finding_with_destructured_id_match() {
        let source = r#"
            fn reply(deps: DepsMut, _env: Env, msg: Reply) -> StdResult<Response> {
                let Reply { id, result, .. } = msg;
                match id {
                    1 => handle_pool_created(deps, result),
                    2 => handle_swap_result(deps, result),
                    _ => Err(StdError::generic_err("unexpected reply")),
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when Reply is destructured and id is matched"
        );
    }

    #[test]
    fn test_destructure_without_id_discrimination_still_flags() {
        // Destructures Reply but never discriminates on id — a genuine bug, must fire.
        let source = r#"
            fn reply(deps: DepsMut, _env: Env, msg: Reply) -> StdResult<Response> {
                let Reply { result, .. } = msg;
                let data = result.into_result().map_err(StdError::generic_err)?;
                CHILD.save(deps.storage, &data.unwrap_or_default())?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Destructuring Reply without matching on id is still a bug"
        );
    }

    // --- FP idx 3: mock reply handler in test scaffolding ---
    #[test]
    fn test_no_finding_for_mock_handler_in_tests_dir() {
        let source = r#"
            fn reply(_deps: DepsMut, _env: Env, msg: Reply) -> StdResult<Response> {
                Ok(Response::new()
                    .add_attribute("mock", "reply")
                    .set_data(msg.result.unwrap().data.unwrap_or_default()))
            }
        "#;
        let findings = run_detector_at(source, "tests/integration.rs");
        assert!(
            findings.is_empty(),
            "Should not flag mock reply handlers in integration test files"
        );
    }

    #[test]
    fn test_no_finding_for_reply_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                fn reply(_deps: DepsMut, _env: Env, msg: Reply) -> StdResult<Response> {
                    Ok(Response::new()
                        .add_attribute("mock", "reply")
                        .set_data(msg.result.unwrap().data.unwrap_or_default()))
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not descend into #[cfg(test)] modules"
        );
    }

    #[test]
    fn test_reply_in_non_test_module_still_flags() {
        // A real (non-cfg-test) module must still be analyzed.
        let source = r#"
            mod handlers {
                fn reply(deps: DepsMut, env: Env, msg: Reply) -> StdResult<Response> {
                    let result = msg.result.into_result().map_err(StdError::generic_err)?;
                    let event = result.events.iter().find(|e| e.ty == "wasm").unwrap();
                    CHILD.save(deps.storage, &event.attributes[0].value)?;
                    Ok(Response::new())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Reply handlers in ordinary modules must still be flagged"
        );
    }

    // --- Partial mitigation for FP idx 1: same-file delegation to an id-checking handler ---
    #[test]
    fn test_no_finding_when_same_file_callee_checks_id() {
        let source = r#"
            fn reply(deps: DepsMut, env: Env, msg: Reply) -> Result<Response, ContractError> {
                handle_reply(deps, env, msg).map_err(ContractError::from)
            }

            fn handle_reply(deps: DepsMut, env: Env, msg: Reply) -> StdResult<Response> {
                match msg.id {
                    INSTANTIATE_REPLY_ID => on_instantiate(deps, msg),
                    id => Err(StdError::generic_err(format!("unknown reply id {}", id))),
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the forwarded same-file handler checks msg.id"
        );
    }

    #[test]
    fn test_delegation_to_callee_without_id_check_still_flags() {
        // Forwards to a same-file callee that ALSO fails to discriminate — must fire.
        let source = r#"
            fn reply(deps: DepsMut, env: Env, msg: Reply) -> Result<Response, ContractError> {
                handle_reply(deps, env, msg).map_err(ContractError::from)
            }

            fn handle_reply(deps: DepsMut, env: Env, msg: Reply) -> StdResult<Response> {
                let result = msg.result.into_result().map_err(StdError::generic_err)?;
                let data = result.events[0].attributes[0].value.clone();
                CHILD.save(deps.storage, &data)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Delegation to a handler that also lacks an id check must still fire"
        );
    }
}
