use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ImplItemFn, ItemFn, ItemMod};

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

/// True if `attrs` carries a `#[cfg(test)]` (or `#[cfg(all(test, ...))]`) marker.
fn has_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path().is_ident("cfg") && {
            // Token-level check: `test` appears as an identifier inside the cfg.
            let tokens = attr.meta.to_token_stream().to_string();
            tokens
                .split(|c: char| !(c.is_alphanumeric() || c == '_'))
                .any(|t| t == "test")
        }
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
