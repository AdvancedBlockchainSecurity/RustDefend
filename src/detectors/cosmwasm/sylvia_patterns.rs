use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ExprCall, ExprMethodCall, ImplItemFn, ItemFn};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct SylviaPatternDetector;

impl Detector for SylviaPatternDetector {
    fn id(&self) -> &'static str {
        "CW-012"
    }
    fn name(&self) -> &'static str {
        "sylvia-pattern-issues"
    }
    fn description(&self) -> &'static str {
        "Detects Sylvia contract methods with #[sv::msg(exec)] attribute missing authorization checks"
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

        // Build a map of every function/method definition in the file (both free
        // functions and impl methods) so we can resolve the *body* of any helper
        // an exec method delegates its authorization to. This is used to soundly
        // suppress the "auth-in-shared-helper" false positive without a blanket
        // name-based skip: we only treat the method as authorized when we can
        // actually see the callee's body and confirm it contains a real check.
        let mut def_collector = DefCollector {
            defs: HashMap::new(),
        };
        def_collector.visit_file(&ctx.ast);

        let mut visitor = SylviaVisitor {
            findings: &mut findings,
            ctx,
            defs: &def_collector.defs,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Authorization tokens matched directly in an exec method body (mirrors the
/// detector's historical, deliberately broad definition of "an auth check is present").
const AUTH_PATTERNS: &[&str] = &[
    "info . sender",
    "info.sender",
    "deps . api . addr_validate",
    "deps.api.addr_validate",
    "ensure !",
    "ensure!",
    "require !",
    "require!",
    "assert !",
    "assert!",
    "admin",
    "owner",
];

/// Stronger auth tokens required inside a *resolved callee* body before we accept
/// that a delegated helper actually performs authorization. Intentionally excludes
/// the bare "admin"/"owner" substrings (which also match plain getters/fields) so
/// that resolving a non-checking helper never silences a real vulnerability.
const CALLEE_AUTH_PATTERNS: &[&str] = &[
    "info . sender",
    "info.sender",
    "addr_validate",
    "ensure !",
    "ensure!",
    "require !",
    "require!",
    "assert !",
    "assert!",
];

/// cw_utils payment-validation calls. A method that validates attached funds and
/// only credits what the caller actually sent is permissionless by design — there
/// is no privilege for an authorization check to protect.
const PAYMENT_VALIDATION: &[&str] = &["must_pay", "may_pay", "one_coin"];

/// A resolved function/method definition: its body token text and the names it calls.
struct FnDef {
    body_src: String,
    calls: Vec<String>,
}

/// Collects every function/method definition in the file, keyed by identifier.
struct DefCollector {
    defs: HashMap<String, Vec<FnDef>>,
}

impl DefCollector {
    fn add(&mut self, name: String, block: &syn::Block) {
        let body_src = block.to_token_stream().to_string();
        let calls = collect_call_names(block);
        self.defs
            .entry(name)
            .or_default()
            .push(FnDef { body_src, calls });
    }
}

impl<'ast> Visit<'ast> for DefCollector {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        self.add(func.sig.ident.to_string(), &func.block);
        syn::visit::visit_item_fn(self, func);
    }

    fn visit_impl_item_fn(&mut self, func: &'ast ImplItemFn) {
        self.add(func.sig.ident.to_string(), &func.block);
        syn::visit::visit_impl_item_fn(self, func);
    }
}

/// Collect the names of all functions/methods called inside a block.
fn collect_call_names(block: &syn::Block) -> Vec<String> {
    struct CallNames {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for CallNames {
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            let name = node.method.to_string();
            if !self.names.contains(&name) {
                self.names.push(name);
            }
            syn::visit::visit_expr_method_call(self, node);
        }
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
    let mut c = CallNames { names: Vec::new() };
    c.visit_block(block);
    c.names
}

const MAX_RESOLVE_DEPTH: usize = 4;

/// Returns true if any resolvable callee (transitively, bounded depth) contains a
/// real authorization check. Only suppresses when a check is actually *seen* in a
/// resolved body, so a call chain with no check anywhere still produces a finding.
fn callees_have_auth(
    defs: &HashMap<String, Vec<FnDef>>,
    calls: &[String],
    visited: &mut Vec<String>,
    depth: usize,
) -> bool {
    if depth >= MAX_RESOLVE_DEPTH {
        return false;
    }
    for name in calls {
        if visited.contains(name) {
            continue;
        }
        if let Some(fn_defs) = defs.get(name) {
            for def in fn_defs {
                if CALLEE_AUTH_PATTERNS
                    .iter()
                    .any(|p| def.body_src.contains(p))
                {
                    return true;
                }
            }
            visited.push(name.clone());
            for def in fn_defs {
                if callees_have_auth(defs, &def.calls, visited, depth + 1) {
                    return true;
                }
            }
        }
    }
    false
}

/// Determine whether a save/update/remove method call actually targets contract
/// storage (cw_storage_plus), rather than mutating a caller-supplied local
/// collection (`Vec::remove`, `HashMap::insert`, etc.).
///
/// cw_storage_plus `Item`/`Map` writes always pass a storage handle as their first
/// argument (`deps.storage` / `ctx.deps.storage`) and are invoked on a struct field
/// (`self.<field>.save(..)`). A local `entries.remove(0)` matches neither.
fn is_storage_write(node: &ExprMethodCall) -> bool {
    let method = node.method.to_string();
    if method != "save" && method != "update" && method != "remove" {
        return false;
    }
    let args_src = node.args.to_token_stream().to_string();
    if args_src.contains("storage") {
        return true;
    }
    let receiver_src = node.receiver.to_token_stream().to_string();
    receiver_src.contains("self")
}

/// True if the function body performs at least one real storage write.
fn has_storage_write(func: &ItemFn) -> bool {
    struct WriteFinder {
        found: bool,
    }
    impl<'ast> Visit<'ast> for WriteFinder {
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            if is_storage_write(node) {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, node);
        }
    }
    let mut wf = WriteFinder { found: false };
    wf.visit_block(&func.block);
    wf.found
}

/// True if the function carries a test attribute (`#[test]`, `#[tokio::test]`,
/// `#[ink::test]`) or is gated behind `#[cfg(test)]`.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if let Some(seg) = attr.path().segments.last() {
            if seg.ident == "test" {
                return true;
            }
        }
        if attr.path().is_ident("cfg") {
            return attr.meta.to_token_stream().to_string().contains("test");
        }
        false
    })
}

struct SylviaVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    defs: &'a HashMap<String, Vec<FnDef>>,
}

impl<'ast, 'a> Visit<'ast> for SylviaVisitor<'a> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Check if function has #[sv::msg(exec)] attribute
        let has_sv_exec = func.attrs.iter().any(|attr| {
            let tokens = attr.meta.to_token_stream().to_string();
            tokens.contains("sv :: msg (exec)") || tokens.contains("sv::msg(exec)")
        });

        if !has_sv_exec {
            return;
        }

        // Never analyze test code as production surface.
        if is_test_fn(&func.attrs) {
            return;
        }

        // Skip functions that don't actually write to contract storage. A
        // save/update/remove on a local Vec/HashMap is not a persistent mutation,
        // so the "storage writes but no auth" premise does not apply.
        if !has_storage_write(func) {
            return;
        }

        let body_src = fn_body_source(func);

        // Direct, inline authorization tokens.
        let mut has_auth = AUTH_PATTERNS.iter().any(|p| body_src.contains(p));

        // Delegated authorization: resolve helper bodies (self.assert_authorized(&ctx)?,
        // check_permissions(...), etc.) and accept only when a real check is visible in
        // a resolved callee. If the helper lives in another file and cannot be resolved,
        // we do NOT suppress — the finding still fires (no false negative).
        if !has_auth {
            let calls = collect_call_names(&func.block);
            let mut visited = Vec::new();
            has_auth = callees_have_auth(self.defs, &calls, &mut visited, 0);
        }

        if has_auth {
            return;
        }

        // Permissionless-by-design flows (deposit / claim / register) that validate
        // attached funds with cw_utils only credit what the caller actually sent —
        // there is no privilege to protect, so an authorization check is not required.
        if PAYMENT_VALIDATION.iter().any(|p| body_src.contains(p)) {
            return;
        }

        let fn_name = func.sig.ident.to_string();
        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "CW-012".to_string(),
            name: "sylvia-pattern-issues".to_string(),
            severity: Severity::Medium,
            confidence: Confidence::Medium,
            message: format!(
                "Sylvia exec method '{}' has storage writes but no authorization check",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add authorization check (e.g., ensure!(info.sender == admin)) to Sylvia exec method before state mutations".to_string(),
            chain: Chain::CosmWasm,
        });
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
        SylviaPatternDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_exec_without_auth() {
        let source = r#"
            #[sv::msg(exec)]
            fn update_config(&self, ctx: ExecCtx, new_val: u64) -> StdResult<Response> {
                self.config.save(ctx.deps.storage, &Config { val: new_val })?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect exec method without auth check"
        );
        assert_eq!(findings[0].detector_id, "CW-012");
    }

    #[test]
    fn test_no_finding_with_sender_check() {
        let source = r#"
            #[sv::msg(exec)]
            fn update_config(&self, ctx: ExecCtx, info: MessageInfo, new_val: u64) -> StdResult<Response> {
                if info.sender != self.admin {
                    return Err(StdError::generic_err("unauthorized"));
                }
                self.config.save(ctx.deps.storage, &Config { val: new_val })?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag exec method with sender check"
        );
    }

    // FP idx 0: authorization delegated to a resolvable helper.
    #[test]
    fn test_no_finding_auth_delegated_to_helper() {
        let source = r#"
            #[sv::msg(exec)]
            fn pause(&self, ctx: ExecCtx) -> StdResult<Response> {
                self.assert_authorized(&ctx)?;
                self.paused.save(ctx.deps.storage, &true)?;
                Ok(Response::new())
            }

            fn assert_authorized(&self, ctx: &ExecCtx) -> StdResult<()> {
                ensure!(ctx.info.sender == self.gov.load(ctx.deps.storage)?, StdError::generic_err("unauthorized"));
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag exec method whose resolvable helper performs the auth check"
        );
    }

    // FN guard for idx 0: a resolvable helper that performs NO check must still fire.
    #[test]
    fn test_still_fires_when_helper_has_no_auth() {
        let source = r#"
            #[sv::msg(exec)]
            fn set_thing(&self, ctx: ExecCtx, v: u64) -> StdResult<Response> {
                self.prepare(&ctx)?;
                self.thing.save(ctx.deps.storage, &v)?;
                Ok(Response::new())
            }

            fn prepare(&self, ctx: &ExecCtx) -> StdResult<()> {
                let _ = ctx;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag when the delegated helper performs no authorization"
        );
    }

    // FP idx 1: permissionless deposit validated with cw_utils::must_pay.
    #[test]
    fn test_no_finding_permissionless_deposit() {
        let source = r#"
            #[sv::msg(exec)]
            fn deposit(&self, ctx: ExecCtx) -> StdResult<Response> {
                let amount = must_pay(&ctx.info, "uatom")?;
                self.total_deposits
                    .update(ctx.deps.storage, |t: Uint128| -> StdResult<_> { Ok(t + amount) })?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag permissionless deposit that validates attached funds"
        );
    }

    // FP idx 2: .remove() on a caller-supplied local Vec is not a storage write.
    #[test]
    fn test_no_finding_local_collection_mutation() {
        let source = r#"
            #[sv::msg(exec)]
            fn submit(&self, ctx: ExecCtx, mut entries: Vec<String>) -> StdResult<Response> {
                entries.remove(0);
                let attrs: Vec<Attribute> = entries.into_iter().map(|e| attr("entry", e)).collect();
                Ok(Response::new().add_attributes(attrs))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a method that only mutates a local collection, not storage"
        );
    }
}
