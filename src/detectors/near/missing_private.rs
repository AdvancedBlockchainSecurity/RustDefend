use quote::ToTokens;
use std::collections::HashSet;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{
    Attribute, BinOp, Block, Expr, ExprCall, ExprIf, ExprMethodCall, FnArg, ImplItemFn, ItemImpl,
    ItemMod, Local, Macro, Token, Visibility,
};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingPrivateDetector;

impl Detector for MissingPrivateDetector {
    fn id(&self) -> &'static str {
        "NEAR-006"
    }
    fn name(&self) -> &'static str {
        "missing-private-callback"
    }
    fn description(&self) -> &'static str {
        "Detects public callback methods (on_* / *_callback) without #[private] attribute"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Near
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Require NEAR-specific source markers to avoid cross-chain FPs
        if !ctx.source.contains("near_sdk")
            && !ctx.source.contains("near_contract_standards")
            && !ctx.source.contains("#[near_bindgen]")
            && !ctx.source.contains("#[near(")
            && !ctx.source.contains("env::predecessor_account_id")
            && !ctx.source.contains("env::signer_account_id")
            && !ctx.source.contains("Promise::new")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let guard_helpers = collect_guard_helpers(&ctx.ast);
        let mut visitor = PrivateVisitor {
            findings: &mut findings,
            ctx,
            guard_helpers,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct PrivateVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    /// Names of in-file helpers whose bodies perform a self-call check.
    guard_helpers: HashSet<String>,
}

/// Returns true if the impl block is a NEAR contract impl, i.e. it carries
/// `#[near_bindgen]` (near-sdk 4) or `#[near]` / `#[near(...)]` (near-sdk 5).
/// Only methods inside such an impl become on-chain entry points; a `pub`
/// method on a plain internal helper struct is ordinary intra-crate Rust API
/// surface that no external account can invoke, so `#[private]` is meaningless
/// there. We match on the last path segment so fully-qualified forms such as
/// `#[near_sdk::near_bindgen]` are still recognised (avoids false negatives).
fn impl_is_contract(node: &ItemImpl) -> bool {
    node.attrs.iter().any(|attr| {
        if let Some(seg) = attr.path().segments.last() {
            let id = seg.ident.to_string();
            id == "near_bindgen" || id == "near"
        } else {
            false
        }
    })
}

/// Returns true if the attribute list contains a `#[cfg(test)]` gate.
/// Code under `#[cfg(test)]` is stripped from the deployed WASM and has no
/// on-chain attack surface, so callbacks on test mocks must not be flagged.
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if attr.path().is_ident("cfg") {
            let tokens = attr.meta.to_token_stream().to_string();
            tokens.contains("test")
        } else {
            false
        }
    })
}

/// Returns true if the method carries evidence that it actually consumes a
/// cross-contract promise result (and is therefore a genuine callback): either
/// a `#[callback_unwrap]` / `#[callback_result]` parameter attribute, or a body
/// that reads promise results. Used to gate weak name matches (`handle_*` and
/// bare `callback` substrings) so ordinary entry points / config setters named
/// after a `callback_*` storage field are not misclassified as callbacks.
fn has_callback_evidence(method: &ImplItemFn, body_src: &str) -> bool {
    if body_src.contains("promise_result")
        || body_src.contains("promise_results_count")
        || body_src.contains("PromiseResult")
    {
        return true;
    }
    method.sig.inputs.iter().any(|arg| {
        if let FnArg::Typed(pat) = arg {
            pat.attrs.iter().any(|a| {
                if let Some(id) = a.path().get_ident() {
                    id == "callback_unwrap" || id == "callback_result"
                } else {
                    false
                }
            })
        } else {
            false
        }
    })
}

/// Returns true if `expr` structurally contains an actual *call* to `name`,
/// e.g. `env::predecessor_account_id()` or `self.current_account_id()`. A bare
/// mention of the identifier — a log/format string, a struct field, a path that
/// is never invoked — does not count. Matching on the last path segment keeps
/// both `env::foo()` and an imported `foo()` recognised.
fn expr_calls(expr: &Expr, name: &str) -> bool {
    struct CallFinder<'n> {
        name: &'n str,
        found: bool,
    }
    impl<'ast, 'n> Visit<'ast> for CallFinder<'n> {
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Expr::Path(p) = &*node.func {
                if p.path.segments.last().is_some_and(|s| s.ident == self.name) {
                    self.found = true;
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            if node.method == self.name {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, node);
        }
    }
    let mut finder = CallFinder { name, found: false };
    finder.visit_expr(expr);
    finder.found
}

/// Returns true if `lhs` and `rhs` are the two sides of a genuine self-call
/// check: one side invokes `predecessor_account_id()` and the other invokes
/// `current_account_id()` (in either order). This is the structural core of
/// what `#[private]` expands to — the two values must actually meet as
/// operands, not merely both occur somewhere in the body.
fn is_self_comparison(lhs: &Expr, rhs: &Expr) -> bool {
    (expr_calls(lhs, "predecessor_account_id") && expr_calls(rhs, "current_account_id"))
        || (expr_calls(lhs, "current_account_id") && expr_calls(rhs, "predecessor_account_id"))
}

/// Returns true if `expr` contains an `==` / `!=` comparison whose operands are
/// the predecessor and current account ids.
fn contains_self_comparison(expr: &Expr) -> bool {
    struct CmpFinder {
        found: bool,
    }
    impl<'ast> Visit<'ast> for CmpFinder {
        fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
            if matches!(node.op, BinOp::Eq(_) | BinOp::Ne(_))
                && is_self_comparison(&node.left, &node.right)
            {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, node);
        }
    }
    let mut finder = CmpFinder { found: false };
    finder.visit_expr(expr);
    finder.found
}

/// Parses a macro's arguments as a comma-separated expression list. Returns an
/// empty vec for macros whose body is not an expression list (e.g. `vec![..;n]`).
fn macro_args(mac: &Macro) -> Vec<Expr> {
    mac.parse_body_with(Punctuated::<Expr, Token![,]>::parse_terminated)
        .map(|args| args.into_iter().collect())
        .unwrap_or_default()
}

/// Returns true if the block cannot fall through to the code that follows it —
/// it panics or returns. Used to confirm that an `if` testing the caller is a
/// real guard rather than a branch that merely varies behaviour.
fn block_diverges(block: &Block) -> bool {
    struct DivergeFinder {
        found: bool,
    }
    impl<'ast> Visit<'ast> for DivergeFinder {
        fn visit_expr_return(&mut self, _node: &'ast syn::ExprReturn) {
            self.found = true;
        }
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Expr::Path(p) = &*node.func {
                if p.path
                    .segments
                    .last()
                    .is_some_and(|s| s.ident == "panic_str" || s.ident == "abort")
                {
                    self.found = true;
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
        fn visit_macro(&mut self, node: &'ast Macro) {
            if node.path.segments.last().is_some_and(|s| {
                s.ident == "panic" || s.ident == "unreachable" || s.ident == "env_panic"
            }) {
                self.found = true;
            }
            syn::visit::visit_macro(self, node);
        }
    }
    let mut finder = DivergeFinder { found: false };
    finder.visit_block(block);
    finder.found
}

/// Returns true if the body enforces a hand-rolled self-call guard equivalent
/// to the `#[private]` expansion. Unlike a substring scan, this requires the
/// check to be *performed*, in one of the shapes it actually takes:
///
///   * `require!/assert!(predecessor == current, ..)` — the comparison is the
///     macro's condition;
///   * `assert_eq!(predecessor, current)` — the two ids are the compared args;
///   * `if predecessor != current { panic/return }` — an if-guard that diverges;
///   * `let is_self = predecessor == current; require!(is_self)` — the
///     comparison is bound to a local that is later tested;
///   * `self.assert_self()` — an actual *call* to a helper that we resolved, in
///     this file, to a body performing the comparison above (or to the
///     conventional `assert_self` name when the helper lives out of file).
///
/// Merely *mentioning* `predecessor_account_id()` (a log line) and
/// `current_account_id()` (building a `Self::ext(..)` promise) in the same body
/// is not a guard and must stay reported.
fn has_manual_self_guard(block: &Block, guard_helpers: &HashSet<String>) -> bool {
    struct GuardFinder<'a> {
        guard_helpers: &'a HashSet<String>,
        /// Locals bound directly to a self-comparison, e.g. `let is_self = ..`.
        self_flags: HashSet<String>,
        found: bool,
    }

    impl<'a> GuardFinder<'a> {
        /// True if `expr` tests the caller: either the comparison inline, or a
        /// local previously bound to that comparison.
        fn is_self_condition(&self, expr: &Expr) -> bool {
            if contains_self_comparison(expr) {
                return true;
            }
            let src = expr.to_token_stream().to_string();
            self.self_flags.iter().any(|flag| {
                src.split(|c: char| !c.is_alphanumeric() && c != '_')
                    .any(|t| t == flag)
            })
        }

        /// True if a call to `name` reaches a body that performs the guard.
        fn callee_guards(&self, name: &str) -> bool {
            self.guard_helpers.contains(name) || name == "assert_self"
        }
    }

    impl<'ast, 'a> Visit<'ast> for GuardFinder<'a> {
        fn visit_local(&mut self, node: &'ast Local) {
            if let (Some(init), syn::Pat::Ident(id)) = (&node.init, &node.pat) {
                if contains_self_comparison(&init.expr) {
                    self.self_flags.insert(id.ident.to_string());
                }
            }
            syn::visit::visit_local(self, node);
        }

        fn visit_macro(&mut self, node: &'ast Macro) {
            let name = node
                .path
                .segments
                .last()
                .map(|s| s.ident.to_string())
                .unwrap_or_default();
            let args = macro_args(node);
            match name.as_str() {
                // `require!(cond, ..)` / `assert!(cond, ..)` — arg 0 is the condition.
                "require" | "assert" | "debug_assert" => {
                    if args.first().is_some_and(|c| self.is_self_condition(c)) {
                        self.found = true;
                    }
                }
                // `assert_eq!(predecessor, current)` — the ids are the operands.
                "assert_eq" | "debug_assert_eq" => {
                    if args.len() >= 2 && is_self_comparison(&args[0], &args[1]) {
                        self.found = true;
                    }
                }
                _ => {}
            }
            syn::visit::visit_macro(self, node);
        }

        fn visit_expr_if(&mut self, node: &'ast ExprIf) {
            // Only an if whose taken branch panics or returns is a guard; one
            // that merely varies behaviour leaves the callback reachable.
            if self.is_self_condition(&node.cond) {
                let else_diverges = node.else_branch.as_ref().is_some_and(|(_, e)| {
                    if let Expr::Block(b) = &**e {
                        block_diverges(&b.block)
                    } else {
                        false
                    }
                });
                if block_diverges(&node.then_branch) || else_diverges {
                    self.found = true;
                }
            }
            syn::visit::visit_expr_if(self, node);
        }

        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Expr::Path(p) = &*node.func {
                if let Some(seg) = p.path.segments.last() {
                    if self.callee_guards(&seg.ident.to_string()) {
                        self.found = true;
                    }
                }
            }
            syn::visit::visit_expr_call(self, node);
        }

        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            if self.callee_guards(&node.method.to_string()) {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, node);
        }
    }

    let mut finder = GuardFinder {
        guard_helpers,
        self_flags: HashSet::new(),
        found: false,
    };
    finder.visit_block(block);
    finder.found
}

/// Collects the names of functions/methods in this file whose bodies perform a
/// self-call check, so that a *call* to one of them counts as a guard at the
/// call site. Resolution is name-based only because a call is what we match —
/// the callee's body must still contain the structural comparison.
fn collect_guard_helpers(file: &syn::File) -> HashSet<String> {
    struct HelperCollector {
        names: HashSet<String>,
    }
    impl HelperCollector {
        fn record(&mut self, name: String, block: &Block) {
            // Empty helper set: a helper only qualifies on its own comparison,
            // never by transitively calling another helper (avoids recursion).
            if has_manual_self_guard(block, &HashSet::new()) {
                self.names.insert(name);
            }
        }
    }
    impl<'ast> Visit<'ast> for HelperCollector {
        fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
            self.record(node.sig.ident.to_string(), &node.block);
            syn::visit::visit_item_fn(self, node);
        }
        fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
            self.record(node.sig.ident.to_string(), &node.block);
            syn::visit::visit_impl_item_fn(self, node);
        }
    }
    let mut collector = HelperCollector {
        names: HashSet::new(),
    };
    collector.visit_file(file);
    collector.names
}

impl<'ast, 'a> Visit<'ast> for PrivateVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Skip #[cfg(test)] modules entirely — their contents never reach WASM.
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        // Only methods inside a #[near_bindgen] / #[near] contract impl are
        // exported as on-chain entry points and can be reached by an attacker.
        // Plain helper-struct impls carry no callback attack surface.
        if !impl_is_contract(node) {
            return;
        }
        syn::visit::visit_item_impl(self, node);
    }

    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        let fn_name = method.sig.ident.to_string();

        let body_src = method.block.to_token_stream().to_string();

        // Strong callback naming conventions: `on_*` and `*_callback` are the
        // NEAR conventions for `.then()`-registered promise callbacks.
        let strong_signal = fn_name.starts_with("on_") || fn_name.ends_with("_callback");

        // Weak name signals — `handle_*` is a common name for ordinary public
        // entry points, and a bare `callback` substring matches config fields
        // like `callback_gas`. Require actual promise-result evidence before
        // treating these as callbacks.
        let weak_signal = fn_name.starts_with("handle_") || fn_name.contains("callback");

        let is_callback =
            strong_signal || (weak_signal && has_callback_evidence(method, &body_src));

        if !is_callback {
            return;
        }

        // Check if it's public
        let is_public = matches!(method.vis, Visibility::Public(_));
        if !is_public {
            return;
        }

        // Check for #[private] attribute
        let has_private = has_attribute(&method.attrs, "private");
        if has_private {
            return;
        }

        // A hand-rolled self-call guard that is actually *performed* is
        // equivalent to the #[private] expansion — the callback is protected.
        // Merely naming the two account ids somewhere in the body is not.
        if has_manual_self_guard(&method.block, &self.guard_helpers) {
            return;
        }

        let line = span_to_line(&method.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "NEAR-006".to_string(),
            name: "missing-private-callback".to_string(),
            severity: Severity::Critical,
            confidence: Confidence::High,
            message: format!(
                "Callback method '{}' is public without #[private] attribute",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&method.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation:
                "Add #[private] attribute to ensure only the contract itself can call this callback"
                    .to_string(),
            chain: Chain::Near,
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
            Chain::Near,
            std::collections::HashMap::new(),
        );
        MissingPrivateDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_private() {
        let source = r#"
            use near_sdk::env;
            #[near_bindgen]
            impl Contract {
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing #[private]");
    }

    #[test]
    fn test_no_finding_with_private() {
        let source = r#"
            impl Contract {
                #[private]
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with #[private]");
    }

    // A genuine `*_callback` callback in a contract impl without #[private]
    // must still fire (guards against over-suppression / false negatives).
    #[test]
    fn test_detects_missing_private_suffix() {
        let source = r#"
            use near_sdk::near_bindgen;
            #[near_bindgen]
            impl Contract {
                pub fn withdraw_callback(&mut self, amount: U128) {
                    self.total -= amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect missing #[private] on *_callback"
        );
    }

    // A genuine `handle_*` callback that reads a promise result must still
    // fire — the weak-name evidence gate keeps real callbacks detectable.
    #[test]
    fn test_detects_handle_callback_with_promise_evidence() {
        let source = r#"
            use near_sdk::env;
            #[near_bindgen]
            impl Contract {
                pub fn handle_swap(&mut self) {
                    let _r = env::promise_result(0);
                    self.total += 1;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "handle_* callback consuming a promise result should be flagged"
        );
    }

    // FP idx 0: pub method on a plain internal helper struct (no #[near_bindgen]).
    #[test]
    fn test_no_finding_on_non_bindgen_helper_struct() {
        let source = r#"
            use near_sdk::near_bindgen;

            pub struct EventRouter;

            impl EventRouter {
                pub fn handle_event(&self, e: &str) -> bool {
                    e.starts_with("transfer")
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "pub method on a non-#[near_bindgen] helper struct is not an entry point"
        );
    }

    // FP idx 1: callback with a hand-rolled self-call guard (manual #[private]).
    #[test]
    fn test_no_finding_with_manual_self_guard() {
        let source = r#"
            use near_sdk::env;
            #[near_bindgen]
            impl Contract {
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    require!(
                        env::predecessor_account_id() == env::current_account_id(),
                        "Only the contract itself can call this callback"
                    );
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "hand-rolled self-call guard is equivalent to #[private]"
        );
    }

    // MUST STILL FLAG (regression guard for the ADV-206 over-skip).
    // A genuinely unprotected callback that merely *mentions* both account ids:
    // `predecessor_account_id()` feeds an audit log and `current_account_id()`
    // builds a follow-up `Self::ext(..)` promise. Neither is a check — the two
    // values never meet as comparison operands — so any account can call this
    // directly and drain the vault. The substring guard silenced it.
    #[test]
    fn test_still_flags_callback_mentioning_account_ids_without_comparison() {
        let source = r#"
            use near_sdk::{env, near_bindgen, AccountId, Promise};
            #[near_bindgen]
            impl Vault {
                pub fn on_withdraw_complete(&mut self, account_id: AccountId, amount: U128) -> Promise {
                    let caller = env::predecessor_account_id();
                    env::log_str(&format!("withdraw_complete caller={}", caller));

                    let bal = self.balances.get(&account_id).unwrap_or(0);
                    self.balances.insert(&account_id, &(bal.saturating_sub(amount.0)));

                    Promise::new(account_id).transfer(amount.0).then(
                        Self::ext(env::current_account_id()).on_settled(),
                    )
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "callback that only mentions predecessor/current account ids (log + Self::ext) \
             performs no self-call check and must still be flagged"
        );
    }

    // MUST STILL FLAG: the two ids are compared, but the `if` only varies
    // behaviour instead of panicking — the callback stays externally reachable.
    #[test]
    fn test_still_flags_self_comparison_that_does_not_guard() {
        let source = r#"
            use near_sdk::{env, near_bindgen};
            #[near_bindgen]
            impl Contract {
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    if env::predecessor_account_id() == env::current_account_id() {
                        self.internal_hits += 1;
                    }
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "a self-comparison whose branch neither panics nor returns is not a guard"
        );
    }

    // A hand-rolled guard written as an if/panic must stay suppressed.
    #[test]
    fn test_no_finding_with_if_panic_self_guard() {
        let source = r#"
            use near_sdk::{env, near_bindgen};
            #[near_bindgen]
            impl Contract {
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    if env::predecessor_account_id() != env::current_account_id() {
                        env::panic_str("callback can only be called by the contract");
                    }
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "if/panic self-call guard is equivalent to #[private]"
        );
    }

    // A guard routed through a local flag must stay suppressed.
    #[test]
    fn test_no_finding_with_let_bound_self_guard() {
        let source = r#"
            use near_sdk::{env, near_bindgen};
            #[near_bindgen]
            impl Contract {
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    let is_self = env::predecessor_account_id() == env::current_account_id();
                    require!(is_self, "only self");
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "self-check bound to a local and asserted is equivalent to #[private]"
        );
    }

    // A guard delegated to an in-file helper whose body performs the check.
    #[test]
    fn test_no_finding_with_resolved_guard_helper() {
        let source = r#"
            use near_sdk::{env, near_bindgen};
            #[near_bindgen]
            impl Contract {
                fn assert_caller_is_self(&self) {
                    require!(
                        env::predecessor_account_id() == env::current_account_id(),
                        "only self"
                    );
                }

                pub fn on_transfer_complete(&mut self, amount: U128) {
                    self.assert_caller_is_self();
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "call to an in-file helper that performs the self-check is a real guard"
        );
    }

    // FP idx 2: config setter/getter whose names merely mention a callback_* field.
    #[test]
    fn test_no_finding_on_callback_named_config_methods() {
        let source = r#"
            use near_sdk::near_bindgen;
            #[near_bindgen]
            impl Contract {
                pub fn set_callback_gas(&mut self, gas: u64) {
                    self.assert_owner();
                    self.callback_gas = gas;
                }

                pub fn get_callback_gas(&self) -> u64 {
                    self.callback_gas
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "callback_gas config accessors are not promise callbacks"
        );
    }

    // FP idx 3: handle_* user-facing entry point (no promise-result evidence).
    #[test]
    fn test_no_finding_on_handle_entry_point() {
        let source = r#"
            use near_sdk::env;
            #[near_bindgen]
            impl Contract {
                #[payable]
                pub fn handle_deposit(&mut self) {
                    let who = env::predecessor_account_id();
                    let amount = env::attached_deposit();
                    self.balances.insert(&who, &amount);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "handle_deposit is a plain entry point, not a promise callback"
        );
    }

    // FP idx 4: mock impl inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            use near_sdk::near_bindgen;

            #[cfg(test)]
            mod tests {
                struct MockReceiver { hits: u32 }

                impl MockReceiver {
                    pub fn on_transfer(&mut self) {
                        self.hits += 1;
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "callbacks on test mocks under #[cfg(test)] have no on-chain surface"
        );
    }
}
