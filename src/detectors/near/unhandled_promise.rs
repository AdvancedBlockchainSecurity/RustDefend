use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;

use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{Attribute, ImplItemFn, ItemFn, ItemMod, Meta, MetaList, Token};

pub struct UnhandledPromiseDetector;

impl Detector for UnhandledPromiseDetector {
    fn id(&self) -> &'static str {
        "NEAR-004"
    }
    fn name(&self) -> &'static str {
        "callback-unwrap-usage"
    }
    fn description(&self) -> &'static str {
        "Detects #[callback_unwrap] usage (should use #[callback_result] with Result)"
    }
    fn severity(&self) -> Severity {
        Severity::High
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

        // Skip SDK infrastructure / macro definition files
        // These define the callback_unwrap attribute itself, not use it
        let path_str = ctx.file_path.to_string_lossy();
        if path_str.contains("/near-sdk-macros/")
            || path_str.contains("/near-sdk/src/")
            || path_str.contains("proc-macro")
            || path_str.contains("derive")
        {
            return Vec::new();
        }

        // Resolve findings against the parsed syn AST rather than raw-source
        // line scanning. A real usage is ALWAYS an actual `#[callback_unwrap]`
        // attribute (on a callback fn or one of its parameters). Matching on
        // AST attribute paths inherently ignores comments, string/raw-string
        // literals, and prose mentions of the token, and lets us skip
        // `#[cfg(test)]` modules and test functions where the token only ever
        // appears as a negative fixture. This loses no true positives because
        // the panic-on-failed-promise behaviour only exists when the SDK-macro
        // attribute is genuinely applied.
        let mut visitor = CallbackUnwrapVisitor {
            findings: Vec::new(),
            source: ctx.source.clone(),
            file_path: ctx.file_path.clone(),
        };
        visitor.visit_file(&ctx.ast);
        visitor.findings
    }
}

/// Truth of a `cfg` predicate evaluated under the assignment `test = false` —
/// i.e. "what does this predicate say about a NON-test (deployed) build?".
/// Every flag other than `test` (features, target_os, ...) is unresolvable
/// here, so it is tracked as `Unknown` and never collapses to a skip.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NonTestBuild {
    /// Predicate is false in every non-test build => the item is test-only.
    Excluded,
    /// Predicate holds in every non-test build => the item is deployed.
    Included,
    /// Depends on flags we cannot resolve; the item may well be deployed.
    Unknown,
}

/// Parse the operands of a `cfg`-style list (`all(a, b)` -> `[a, b]`).
fn cfg_operands(list: &MetaList) -> Option<Vec<Meta>> {
    let parser = Punctuated::<Meta, Token![,]>::parse_terminated;
    parser
        .parse2(list.tokens.clone())
        .ok()
        .map(|ops| ops.into_iter().collect())
}

/// Structurally evaluate a `cfg` predicate with `test` set to false.
///
/// This is what distinguishes `#[cfg(test)]` (test-only, safe to skip) from
/// `#[cfg(not(test))]` (production-only, MUST be scanned). Both mention the
/// `test` identifier; only the predicate's structure tells them apart.
fn eval_in_non_test_build(meta: &Meta) -> NonTestBuild {
    match meta {
        Meta::Path(path) => {
            if path.is_ident("test") {
                NonTestBuild::Excluded
            } else {
                NonTestBuild::Unknown
            }
        }
        // `feature = "x"`, `target_os = "wasm32"`, ... - unresolvable.
        Meta::NameValue(_) => NonTestBuild::Unknown,
        Meta::List(list) => {
            let operands = match cfg_operands(list) {
                Some(ops) => ops,
                None => return NonTestBuild::Unknown,
            };

            if list.path.is_ident("not") {
                // `not` takes exactly one operand; anything else is malformed.
                if operands.len() != 1 {
                    return NonTestBuild::Unknown;
                }
                match eval_in_non_test_build(&operands[0]) {
                    NonTestBuild::Excluded => NonTestBuild::Included,
                    NonTestBuild::Included => NonTestBuild::Excluded,
                    NonTestBuild::Unknown => NonTestBuild::Unknown,
                }
            } else if list.path.is_ident("all") {
                // Conjunction: one false operand excludes the whole item.
                let mut acc = NonTestBuild::Included;
                for operand in &operands {
                    match eval_in_non_test_build(operand) {
                        NonTestBuild::Excluded => return NonTestBuild::Excluded,
                        NonTestBuild::Unknown => acc = NonTestBuild::Unknown,
                        NonTestBuild::Included => {}
                    }
                }
                acc
            } else if list.path.is_ident("any") {
                // Disjunction: one true operand includes the whole item.
                // `any(test, feature = "mock")` stays Unknown - it can still be
                // compiled into a non-test build via the feature.
                let mut acc = NonTestBuild::Excluded;
                for operand in &operands {
                    match eval_in_non_test_build(operand) {
                        NonTestBuild::Included => return NonTestBuild::Included,
                        NonTestBuild::Unknown => acc = NonTestBuild::Unknown,
                        NonTestBuild::Excluded => {}
                    }
                }
                acc
            } else {
                NonTestBuild::Unknown
            }
        }
    }
}

/// True only if `attrs` gate the item OUT of every non-test build, i.e. the
/// item exists solely in `cargo test` builds and is never deployed.
///
/// Deliberately structural rather than textual: `#[cfg(test)]` and
/// `#[cfg(not(test))]` spell the same `test` token but mean opposite things,
/// and only the latter is the deployed code a scanner must never miss.
fn has_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| match &attr.meta {
        Meta::List(list) if list.path.is_ident("cfg") => match cfg_operands(list) {
            // `cfg` carries exactly one predicate.
            Some(ops) if ops.len() == 1 => {
                eval_in_non_test_build(&ops[0]) == NonTestBuild::Excluded
            }
            _ => false,
        },
        _ => false,
    })
}

/// True if `attrs` marks a test function (`#[test]`, `#[tokio::test]`,
/// `#[ink::test]`, `#[near_sdk::test]`, ...) or is `#[cfg(test)]`-gated.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    let is_test_attr = attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .map(|seg| seg.ident == "test")
            .unwrap_or(false)
    });
    is_test_attr || has_cfg_test(attrs)
}

struct CallbackUnwrapVisitor {
    findings: Vec<Finding>,
    source: String,
    file_path: std::path::PathBuf,
}

impl<'ast> Visit<'ast> for CallbackUnwrapVisitor {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Never descend into `#[cfg(test)]` modules: any `callback_unwrap`
        // there is test-only (e.g. a negative lint fixture), not deployed code.
        if has_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        if is_test_fn(&node.attrs) {
            return;
        }
        syn::visit::visit_item_fn(self, node);
    }

    fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
        if is_test_fn(&node.attrs) {
            return;
        }
        syn::visit::visit_impl_item_fn(self, node);
    }

    fn visit_attribute(&mut self, node: &'ast Attribute) {
        // A genuine `#[callback_unwrap]` attribute. This fires for the
        // attribute on a callback fn as well as on a callback parameter
        // (`fn cb(&self, #[callback_unwrap] x: U128)`), because the default
        // AST walk visits parameter attributes too.
        if node.path().is_ident("callback_unwrap") {
            let span = node
                .path()
                .segments
                .first()
                .map(|seg| seg.ident.span())
                .unwrap_or_else(proc_macro2::Span::call_site);
            let line_num = span.start().line.max(1);
            let snippet = self
                .source
                .lines()
                .nth(line_num.saturating_sub(1))
                .unwrap_or("")
                .trim()
                .to_string();

            self.findings.push(Finding {
                detector_id: "NEAR-004".to_string(),
                name: "callback-unwrap-usage".to_string(),
                severity: Severity::High,
                confidence: Confidence::High,
                message: "#[callback_unwrap] will panic on failed promise - use #[callback_result] instead".to_string(),
                file: self.file_path.clone(),
                line: line_num,
                column: 1,
                snippet,
                recommendation: "Replace #[callback_unwrap] with #[callback_result] and handle the Result<T, PromiseError> type".to_string(),
                chain: Chain::Near,
            });
        }
        syn::visit::visit_attribute(self, node);
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
        UnhandledPromiseDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_callback_unwrap() {
        let source = r#"
            use near_sdk::env;
            #[callback_unwrap]
            fn on_transfer_complete(&mut self, amount: U128) {
                self.transferred += amount.0;
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect callback_unwrap");
    }

    #[test]
    fn test_no_finding_callback_result() {
        let source = r#"
            use near_sdk::env;
            #[callback_result]
            fn on_transfer_complete(&mut self, result: Result<U128, PromiseError>) {
                match result {
                    Ok(amount) => self.transferred += amount.0,
                    Err(_) => self.failed += 1,
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag callback_result");
    }

    // --- must_still_fire: attribute on a callback *parameter* ---
    #[test]
    fn test_detects_callback_unwrap_on_parameter() {
        let source = r#"
            use near_sdk::{near_bindgen, json_types::U128};

            #[near_bindgen]
            impl Oracle {
                #[private]
                pub fn on_price(&self, #[callback_unwrap] price: U128) -> U128 {
                    price
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still detect callback_unwrap on a parameter"
        );
    }

    // --- FP1: token only appears in comments (block comment + trailing //) ---
    #[test]
    fn test_no_finding_callback_unwrap_in_comments() {
        let source = r#"
            use near_sdk::env;

            /* Audit note 2024-11: do not use callback_unwrap in this module. */
            impl Contract {
                fn manual_cb(&mut self) {
                    let _r = env::promise_result(0); // safer than callback_unwrap
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag callback_unwrap mentioned only in comments"
        );
    }

    // --- FP2: token inside a raw/plain string in a #[cfg(test)] fixture ---
    #[test]
    fn test_no_finding_callback_unwrap_in_test_fixture_string() {
        let source = r##"
            use near_sdk::near_bindgen;

            #[cfg(test)]
            mod tests {
                #[test]
                fn lint_fixture_rejects_unwrap() {
                    let src = "#[callback_unwrap] fn cb(&mut self, x: U128) {}";
                    assert!(our_ci_lint_fails_on(src));
                }
            }
        "##;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag callback_unwrap text inside a cfg(test) fixture string"
        );
    }

    // --- must_still_fire: production code gated behind `#[cfg(not(test))]` ---
    // `cfg(not(test))` is the DEPLOYED build, not a test fixture. Skipping it
    // because the `test` token appears inside the cfg silences a real vuln:
    // the callback panics on a failed ft_transfer, so the optimistic debit in
    // `withdraw` is never refunded and the user's tokens are destroyed.
    #[test]
    fn test_still_flags_callback_unwrap_in_cfg_not_test_module() {
        let source = r#"
            use near_sdk::{env, near_bindgen, json_types::U128, AccountId, Promise};

            #[cfg(not(test))]
            mod live_withdraw {
                use super::*;

                #[near_bindgen]
                impl Vault {
                    pub fn withdraw(&mut self, amount: U128) -> Promise {
                        let account = env::predecessor_account_id();
                        let balance = self.balances.get(&account).unwrap_or(0);
                        self.balances.insert(&account, &(balance - amount.0));
                        ext_ft::ext(self.token_id.clone())
                            .ft_transfer(account.clone(), amount, None)
                            .then(Self::ext(env::current_account_id())
                                .on_withdraw_complete(account, amount))
                    }

                    #[private]
                    pub fn on_withdraw_complete(
                        &mut self,
                        #[callback_unwrap] _transfer_ok: (),
                        account: AccountId,
                        amount: U128,
                    ) {
                        env::log_str("withdrew");
                    }
                }
            }

            #[cfg(test)]
            mod live_withdraw {
                use super::*;

                #[near_bindgen]
                impl Vault {
                    pub fn withdraw(&mut self, amount: U128) {}
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag callback_unwrap in a #[cfg(not(test))] module - that is deployed code"
        );
    }

    // --- must_still_fire: `test` mentioned in a cfg that still ships ---
    // `any(test, feature = "mock")` compiles into a non-test build whenever the
    // feature is on, so it cannot be treated as test-only.
    #[test]
    fn test_still_flags_callback_unwrap_in_cfg_any_test_or_feature() {
        let source = r#"
            use near_sdk::near_bindgen;

            #[cfg(any(test, feature = "mock"))]
            mod maybe_shipped {
                #[near_bindgen]
                impl Oracle {
                    #[private]
                    pub fn on_price(&self, #[callback_unwrap] price: U128) -> U128 {
                        price
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag callback_unwrap under any(test, feature) - it can ship"
        );
    }

    // --- FP retained: `#[cfg(all(test, ...))]` is still test-only ---
    #[test]
    fn test_no_finding_callback_unwrap_in_cfg_all_test_module() {
        let source = r#"
            use near_sdk::near_bindgen;

            #[cfg(all(test, feature = "integration"))]
            mod tests {
                #[near_bindgen]
                impl Oracle {
                    pub fn on_price(&self, #[callback_unwrap] price: U128) -> U128 {
                        price
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag callback_unwrap in a cfg(all(test, ...)) module"
        );
    }

    // --- FP3: token appears mid-string in a runtime message ---
    #[test]
    fn test_no_finding_callback_unwrap_in_message_string() {
        let source = r#"
            use near_sdk::env;

            impl Contract {
                fn deny_legacy(&self) {
                    env::panic_str("callback_unwrap style callbacks are not supported by this contract");
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag callback_unwrap mentioned only inside a string message"
        );
    }
}
