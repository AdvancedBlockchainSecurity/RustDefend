use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use syn::visit::Visit;

pub struct ReentrancyDetector;

impl Detector for ReentrancyDetector {
    fn id(&self) -> &'static str {
        "INK-001"
    }
    fn name(&self) -> &'static str {
        "ink-reentrancy"
    }
    fn description(&self) -> &'static str {
        "Detects set_allow_reentry(true) which enables reentrancy"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Ink
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Walk the parsed AST rather than raw source lines. This structurally
        // excludes comments and string literals, and it evaluates the actual
        // argument passed to `set_allow_reentry` so that `set_allow_reentry(false)`
        // chained on the same line as another flag set to `true`
        // (e.g. `set_tail_call(true)`) is not misclassified.
        let mut visitor = ReentryVisitor { hits: Vec::new() };
        visitor.visit_file(&ctx.ast);

        let mut findings = Vec::new();
        for hit in visitor.hits {
            let line_text = ctx.line_text(hit.line);
            findings.push(Finding {
                detector_id: "INK-001".to_string(),
                name: "ink-reentrancy".to_string(),
                severity: Severity::Critical,
                confidence: Confidence::High,
                message: "set_allow_reentry(true) enables reentrancy attacks".to_string(),
                file: ctx.file_path.clone(),
                line: hit.line,
                column: hit.column,
                snippet: line_text.trim().to_string(),
                recommendation: "Remove set_allow_reentry(true) unless absolutely necessary. The default (false) prevents reentrancy. If needed, implement a reentrancy guard".to_string(),
                chain: Chain::Ink,
            });
        }

        findings
    }
}

struct ReentryHit {
    line: usize,
    column: usize,
}

struct ReentryVisitor {
    hits: Vec<ReentryHit>,
}

/// Parse the comma-separated predicates inside a `cfg`-like list, e.g. the
/// `test, feature = "std"` of `all(test, feature = "std")`.
fn cfg_predicates(
    list: &syn::MetaList,
) -> Option<syn::punctuated::Punctuated<syn::Meta, syn::Token![,]>> {
    list.parse_args_with(syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated)
        .ok()
}

/// True if the predicate holds *only* in test builds — i.e. it implies `test`.
///
/// This is a structural implication check, not a search for the token `test`.
/// The distinction is the whole point: `#[cfg(not(test))]` mentions `test` but
/// gates the code that ships on-chain, so it must never be treated as test-only.
fn cfg_implies_test(meta: &syn::Meta) -> bool {
    match meta {
        // Bare `test`: compiled in only under `cargo test`.
        syn::Meta::Path(path) => path.is_ident("test"),
        syn::Meta::List(list) => {
            let Some(nested) = cfg_predicates(list) else {
                return false;
            };
            if list.path.is_ident("all") {
                // `all(..)` is a conjunction: one test-only conjunct is enough to
                // confine the whole item to test builds.
                nested.iter().any(cfg_implies_test)
            } else if list.path.is_ident("any") {
                // `any(..)` is a disjunction: test-only only if *every* alternative
                // is, otherwise some non-test build still compiles the item.
                !nested.is_empty() && nested.iter().all(cfg_implies_test)
            } else {
                // `not(..)` never implies `test` for any predicate we model, and an
                // unknown predicate says nothing about test builds.
                false
            }
        }
        // `feature = "std"`, `target_os = "..."`, ... : not a statement about tests.
        syn::Meta::NameValue(_) => false,
    }
}

/// True if the item is test-only scaffolding: `#[test]`, `#[ink::test]`,
/// `#[tokio::test]`, or gated behind a cfg that implies `test`. Such code is
/// never part of the deployed contract, so reentrancy inside it is not a live
/// vulnerability. Production-only gates such as `#[cfg(not(test))]` are *not*
/// test items — that code is exactly what runs on-chain.
fn is_test_item(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let path = attr.path();
        // #[cfg(test)], #[cfg(all(test, ...))], #[cfg(any(test, ink::test))], ...
        if path.is_ident("cfg") {
            return match &attr.meta {
                syn::Meta::List(list) => cfg_predicates(list)
                    .map(|nested| nested.iter().any(cfg_implies_test))
                    .unwrap_or(false),
                _ => false,
            };
        }
        // #[test], #[ink::test], #[tokio::test], #[async_std::test], ...
        matches!(path.segments.last(), Some(seg) if seg.ident == "test")
    })
}

/// True if any argument is the boolean literal `true`. `set_allow_reentry`
/// takes a single bool; a real vulnerability always writes `true` literally,
/// so a non-literal (variable) argument is intentionally not flagged here.
fn has_true_literal_arg(args: &syn::punctuated::Punctuated<syn::Expr, syn::token::Comma>) -> bool {
    args.iter().any(|arg| {
        matches!(
            arg,
            syn::Expr::Lit(syn::ExprLit {
                lit: syn::Lit::Bool(b),
                ..
            }) if b.value
        )
    })
}

impl<'ast> Visit<'ast> for ReentryVisitor {
    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        if is_test_item(&node.attrs) {
            return;
        }
        syn::visit::visit_item_fn(self, node);
    }

    fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
        if is_test_item(&node.attrs) {
            return;
        }
        syn::visit::visit_impl_item_fn(self, node);
    }

    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        if is_test_item(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        if node.method == "set_allow_reentry" && has_true_literal_arg(&node.args) {
            let span = node.method.span();
            self.hits.push(ReentryHit {
                line: span.start().line,
                column: span.start().column + 1,
            });
        }
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if let syn::Expr::Path(path_expr) = &*node.func {
            if let Some(last) = path_expr.path.segments.last() {
                if last.ident == "set_allow_reentry" && has_true_literal_arg(&node.args) {
                    let span = last.ident.span();
                    self.hits.push(ReentryHit {
                        line: span.start().line,
                        column: span.start().column + 1,
                    });
                }
            }
        }
        syn::visit::visit_expr_call(self, node);
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
            Chain::Ink,
            std::collections::HashMap::new(),
        );
        ReentrancyDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_allow_reentry() {
        let source = r#"
            fn call_other(&mut self) {
                self.env().set_allow_reentry(true);
                let result = other_contract.call();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect set_allow_reentry(true)"
        );
    }

    #[test]
    fn test_no_finding_reentry_false() {
        let source = r#"
            fn call_other(&mut self) {
                self.env().set_allow_reentry(false);
                let result = other_contract.call();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag set_allow_reentry(false)"
        );
    }

    // must_still_fire: intentional reentry behind a manual guard is STILL a
    // finding — the vulnerability class (enabling reentry) is present.
    #[test]
    fn test_still_fires_with_manual_guard() {
        let source = r#"
            #[ink(message)]
            pub fn forward_with_callback(&mut self) -> Result<(), Error> {
                if self.locked {
                    return Err(Error::ReentrancyGuard);
                }
                self.locked = true;
                self.env().set_allow_reentry(true);
                let res = self.do_cross_contract_call();
                self.locked = false;
                res
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag set_allow_reentry(true) even with a manual guard"
        );
    }

    // FP idx 0: CallFlags builder chain where set_allow_reentry gets `false`
    // and an unrelated flag (set_tail_call) gets `true` on the same line.
    #[test]
    fn test_no_finding_chained_true_flag() {
        let source = r#"
            fn forward(&mut self) {
                let result = build_call::<DefaultEnvironment>()
                    .call(proxy_target)
                    .call_flags(CallFlags::default().set_allow_reentry(false).set_tail_call(true))
                    .invoke();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when set_allow_reentry gets false and a sibling flag gets true"
        );
    }

    // FP idx 1: mentions in comments, trailing comments, and string literals.
    #[test]
    fn test_no_finding_comments_and_strings() {
        let source = r#"
            fn transfer_safe(&mut self) -> Result<(), Error> {
                // SECURITY: never call set_allow_reentry(true) here; the default (false) is safe.
                self.env().set_allow_reentry(false); // true would enable reentrancy
                return Err(Error::Config("set_allow_reentry(true) is forbidden".into()));
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag set_allow_reentry(true) inside comments or string literals"
        );
    }

    // must_still_fire: `#[cfg(not(test))]` gates the code that SHIPS ON-CHAIN.
    // The test guard must not skip it just because the predicate spells "test".
    #[test]
    fn test_still_flags_cfg_not_test_production_fn() {
        let source = r#"
            #[ink::contract]
            mod vault {
            impl Vault {
                #[cfg(not(test))]
                #[ink(message)]
                pub fn withdraw(&mut self, amount: Balance, callback_target: AccountId) -> Result<(), Error> {
                    let caller = self.env().caller();
                    let bal = self.balances.get(caller).unwrap_or(0);
                    if bal < amount {
                        return Err(Error::InsufficientBalance);
                    }
                    build_call::<DefaultEnvironment>()
                        .call(callback_target)
                        .call_flags(CallFlags::default().set_allow_reentry(true))
                        .returns::<()>()
                        .invoke()
                        .map_err(|_| Error::CallFailed)?;
                    self.balances.insert(caller, &(bal - amount));
                    Ok(())
                }

                #[cfg(test)]
                #[ink(message)]
                pub fn withdraw(&mut self, amount: Balance, _callback_target: AccountId) -> Result<(), Error> {
                    let caller = self.env().caller();
                    let bal = self.balances.get(caller).unwrap_or(0);
                    self.balances.insert(caller, &(bal - amount));
                    Ok(())
                }
            }
            }
        "#;
        let findings = run_detector(source);
        assert_eq!(
            findings.len(),
            1,
            "Should flag set_allow_reentry(true) in a #[cfg(not(test))] production fn"
        );
    }

    // `any(test, feature = "e2e")` still compiles outside test builds when the
    // feature is on, so it is not test-only scaffolding.
    #[test]
    fn test_still_flags_cfg_any_test_or_feature() {
        let source = r#"
            #[cfg(any(test, feature = "e2e"))]
            fn forward(&mut self) {
                self.env().set_allow_reentry(true);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag when the cfg predicate also admits a non-test build"
        );
    }

    // Guard: `all(test, ..)` is still test-only — one test conjunct confines it.
    #[test]
    fn test_no_finding_in_cfg_all_test_fn() {
        let source = r#"
            #[cfg(all(test, feature = "std"))]
            fn helper(&mut self) {
                self.env().set_allow_reentry(true);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag set_allow_reentry(true) inside a #[cfg(all(test, ...))] fn"
        );
    }

    // Guard: reentry enabled only inside #[cfg(test)] code is not a live vuln.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                fn helper(&mut self) {
                    self.env().set_allow_reentry(true);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag set_allow_reentry(true) inside a #[cfg(test)] module"
        );
    }
}
