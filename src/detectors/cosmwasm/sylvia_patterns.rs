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

/// Guard macros whose *condition* may express an authorization check. The macro name
/// alone is meaningless: `ensure!(fee_bps <= MAX)` bounds an argument, `ensure!(
/// info.sender == admin)` bounds the caller. Only the latter is authorization, so these
/// names are just an entry point into inspecting the condition tokens — never a match.
const GUARD_MACROS: &[&str] = &[
    "ensure",
    "ensure_eq",
    "ensure_ne",
    "require",
    "assert",
    "assert_eq",
    "assert_ne",
];

/// Calls that perform an authorization check *on the address handed to them*. Each is
/// accepted only when the caller's identity is among its arguments: `addr_validate(&
/// msg.recipient)` validates an arbitrary address and authorizes nothing, whereas
/// `assert_owner(store, &info.sender)` gates on the caller.
/// Deliberately excludes name-only gates like `assert_authorized` / `check_permissions`:
/// a helper *named* like an authorization gate is not one. Such helpers are handled by
/// resolving and inspecting their bodies instead (see `callees_have_auth`).
const AUTH_CALLS: &[&str] = &[
    "addr_validate",
    "assert_admin",
    "assert_owner",
    "is_admin",
    "is_owner",
];

/// cw_utils payment-validation calls. A method that validates attached funds and
/// only credits what the caller actually sent is permissionless by design — there
/// is no privilege for an authorization check to protect.
const PAYMENT_VALIDATION: &[&str] = &["must_pay", "may_pay", "one_coin"];

/// A resolved function/method definition: its body AST and the names it calls. The body
/// is kept as a `&Block` rather than token text so that delegated authorization can be
/// judged structurally — by what the body *does* — instead of by what it spells.
struct FnDef<'ast> {
    block: &'ast syn::Block,
    calls: Vec<String>,
}

/// Collects every function/method definition in the file, keyed by identifier.
struct DefCollector<'ast> {
    defs: HashMap<String, Vec<FnDef<'ast>>>,
}

impl<'ast> DefCollector<'ast> {
    fn add(&mut self, name: String, block: &'ast syn::Block) {
        let calls = collect_call_names(block);
        self.defs
            .entry(name)
            .or_default()
            .push(FnDef { block, calls });
    }
}

impl<'ast> Visit<'ast> for DefCollector<'ast> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        self.add(func.sig.ident.to_string(), &func.block);
        syn::visit::visit_item_fn(self, func);
    }

    fn visit_impl_item_fn(&mut self, func: &'ast ImplItemFn) {
        self.add(func.sig.ident.to_string(), &func.block);
        syn::visit::visit_impl_item_fn(self, func);
    }
}

/// True if `src` (token text of a single expression) names the caller's identity.
/// Authorization is a statement *about the caller*, so a check that never references
/// the caller cannot be one, whatever it is named.
fn is_caller_identity_src(src: &str) -> bool {
    src.contains("info . sender") || src.contains("info.sender")
}

/// Token-aware ident search, so an alias named `sender` does not match `sender_addr`.
fn mentions_ident(src: &str, ident: &str) -> bool {
    src.split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .any(|t| t == ident)
}

/// Local aliases of the caller's identity (`let sender = ctx.info.sender.clone();`).
/// Real checks routinely compare the alias rather than the original expression, so the
/// alias has to count as the caller for the structural rules below.
fn caller_aliases(block: &syn::Block) -> Vec<String> {
    struct AliasFinder {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for AliasFinder {
        fn visit_local(&mut self, node: &'ast syn::Local) {
            if let Some(init) = &node.init {
                if is_caller_identity_src(&init.expr.to_token_stream().to_string()) {
                    if let syn::Pat::Ident(pat) = &node.pat {
                        self.names.push(pat.ident.to_string());
                    }
                }
            }
            syn::visit::visit_local(self, node);
        }
    }
    let mut f = AliasFinder { names: Vec::new() };
    f.visit_block(block);
    f.names
}

/// True if `src` references the caller, either directly or through a local alias.
fn is_caller(src: &str, aliases: &[String]) -> bool {
    is_caller_identity_src(src) || aliases.iter().any(|a| mentions_ident(src, a))
}

/// Structural test for "this body actually authorizes the caller".
///
/// The caller's identity must appear in a *load-bearing* position — as an operand of an
/// equality comparison, inside the condition of a guard macro, or as an argument to a
/// call that gates on the address it is handed. Presence of an `ensure!`/`assert!` token
/// proves nothing on its own: `ensure!(fee_bps <= MAX)` is an argument bounds-check, not
/// an authorization check, and accepting it silences genuinely unprotected exec methods.
fn block_has_auth_check(block: &syn::Block) -> bool {
    struct AuthFinder {
        aliases: Vec<String>,
        found: bool,
    }
    impl<'ast> Visit<'ast> for AuthFinder {
        fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
            // `info.sender == admin` / `info.sender != owner` — the caller compared
            // against a privileged value.
            if matches!(node.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_)) {
                let left = node.left.to_token_stream().to_string();
                let right = node.right.to_token_stream().to_string();
                if is_caller(&left, &self.aliases) || is_caller(&right, &self.aliases) {
                    self.found = true;
                }
            }
            syn::visit::visit_expr_binary(self, node);
        }

        fn visit_macro(&mut self, node: &'ast syn::Macro) {
            // Guard-macro conditions are unparsed tokens; inspect what is being
            // guarded, not that a guard exists.
            if let Some(seg) = node.path.segments.last() {
                let name = seg.ident.to_string();
                if GUARD_MACROS.contains(&name.as_str())
                    && is_caller(&node.tokens.to_string(), &self.aliases)
                {
                    self.found = true;
                }
            }
            syn::visit::visit_macro(self, node);
        }

        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            // `self.admin.assert_admin(deps.as_ref(), &info.sender)?`
            if AUTH_CALLS.contains(&node.method.to_string().as_str())
                && is_caller(&node.args.to_token_stream().to_string(), &self.aliases)
            {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, node);
        }

        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            // `cw_ownable::assert_owner(deps.storage, &info.sender)?`
            if let syn::Expr::Path(path) = node.func.as_ref() {
                if let Some(seg) = path.path.segments.last() {
                    if AUTH_CALLS.contains(&seg.ident.to_string().as_str())
                        && is_caller(&node.args.to_token_stream().to_string(), &self.aliases)
                    {
                        self.found = true;
                    }
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }
    let mut f = AuthFinder {
        aliases: caller_aliases(block),
        found: false,
    };
    f.visit_block(block);
    f.found
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

/// Returns true if any resolvable callee (transitively, bounded depth) performs a real
/// authorization check. Only suppresses when a check is actually *seen* doing work in a
/// resolved body, so a call chain with no check anywhere still produces a finding — and
/// so does a chain whose helpers merely validate their own arguments.
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
                if block_has_auth_check(def.block) {
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

struct SylviaVisitor<'a, 'ast> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    defs: &'a HashMap<String, Vec<FnDef<'ast>>>,
}

impl<'ast, 'a> Visit<'ast> for SylviaVisitor<'a, 'ast> {
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

    // MUST STILL FLAG: the delegated helper only bounds an *argument*. An `ensure!` in a
    // resolved callee is not authorization unless it ensures something about the caller;
    // keying on the macro token alone silences this genuinely unprotected exec method
    // (anyone can redirect every protocol fee payout). Do not weaken this test.
    #[test]
    fn test_still_flags_helper_that_only_validates_arguments() {
        let source = r#"
            fn validate_fee_bps(fee_bps: Uint128) -> StdResult<()> {
                ensure!(!fee_bps.is_zero() && fee_bps <= Uint128::new(10_000), StdError::generic_err("fee out of range"));
                Ok(())
            }

            #[sv::msg(exec)]
            fn set_fee_collector(&self, ctx: ExecCtx, new_collector: Addr, fee_bps: Uint128) -> StdResult<Response> {
                validate_fee_bps(fee_bps)?;
                self.fee_collector.save(ctx.deps.storage, &new_collector)?;
                self.fee_bps.save(ctx.deps.storage, &fee_bps)?;
                Ok(Response::new().add_attribute("action", "set_fee_collector"))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag when the delegated helper only bounds an argument and never checks the caller"
        );
        assert_eq!(findings[0].detector_id, "CW-012");
        assert!(findings[0].message.contains("set_fee_collector"));
    }

    // MUST STILL FLAG: a helper *named* like an authorization gate that performs no
    // caller check. The name is not the check.
    #[test]
    fn test_still_flags_helper_named_like_auth_gate() {
        let source = r#"
            #[sv::msg(exec)]
            fn set_rate(&self, ctx: ExecCtx, rate: Uint128) -> StdResult<Response> {
                self.assert_authorized(&ctx, rate)?;
                self.rate.save(ctx.deps.storage, &rate)?;
                Ok(Response::new())
            }

            fn assert_authorized(&self, ctx: &ExecCtx, rate: Uint128) -> StdResult<()> {
                ensure!(rate <= Uint128::new(100), StdError::generic_err("rate too high"));
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag a helper named like an auth gate that only checks an argument"
        );
    }

    // Counterpart to the two tests above: the same delegated shape, but the helper does
    // compare the caller. Resolution must still suppress here.
    #[test]
    fn test_no_finding_helper_checks_caller_via_alias() {
        let source = r#"
            #[sv::msg(exec)]
            fn set_fee_collector(&self, ctx: ExecCtx, new_collector: Addr) -> StdResult<Response> {
                self.assert_gov(&ctx)?;
                self.fee_collector.save(ctx.deps.storage, &new_collector)?;
                Ok(Response::new())
            }

            fn assert_gov(&self, ctx: &ExecCtx) -> StdResult<()> {
                let sender = ctx.info.sender.clone();
                let gov = self.gov.load(ctx.deps.storage)?;
                ensure!(sender == gov, StdError::generic_err("unauthorized"));
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the resolved helper compares the caller through a local alias"
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
