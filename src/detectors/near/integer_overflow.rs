use quote::ToTokens;
use syn::visit::Visit;
use syn::{ExprMethodCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct IntegerOverflowDetector;

impl Detector for IntegerOverflowDetector {
    fn id(&self) -> &'static str {
        "NEAR-005"
    }
    fn name(&self) -> &'static str {
        "near-wrapping-arithmetic"
    }
    fn description(&self) -> &'static str {
        "Detects wrapping_*/saturating_* on balance/amount variables"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
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
        let mut visitor = OverflowVisitor {
            findings: &mut findings,
            ctx,
            in_function: false,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct OverflowVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    in_function: bool,
}

/// Returns true if the attributes mark this item as test-only code, i.e.
/// `#[cfg(test)]`, `#[test]`, or a framework test attribute
/// (`#[tokio::test]`, `#[ink::test]`, `#[near_sdk::test]`, ...). Such code is
/// excluded from the release WASM build and never executes on-chain, so
/// intentional overflow edge-case exercises there are not deployable
/// vulnerabilities.
fn is_test_only(attrs: &[syn::Attribute]) -> bool {
    // #[cfg(test)] on a module or fn.
    if has_nested_attribute(attrs, "cfg", "test") {
        return true;
    }
    attrs.iter().any(|attr| {
        // Match the last path segment so that plain `#[test]` as well as
        // `#[tokio::test]`, `#[ink::test]`, `#[near_sdk::test]`, etc. are all
        // treated as test attributes.
        attr.path()
            .segments
            .last()
            .map(|seg| seg.ident == "test")
            .unwrap_or(false)
    })
}

impl<'ast, 'a> Visit<'ast> for OverflowVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Do not descend into test-only modules (`#[cfg(test)] mod tests`).
        // Their arithmetic is compiled out of the deployed contract and often
        // intentionally exercises overflow edge cases.
        if is_test_only(&module.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (`#[test]`, `#[tokio::test]`, `#[ink::test]`,
        // `#[cfg(test)] fn ...`) even if they are not inside a test module.
        if is_test_only(&func.attrs) {
            return;
        }
        self.in_function = true;
        syn::visit::visit_item_fn(self, func);
        self.in_function = false;
    }

    fn visit_expr_method_call(&mut self, call: &'ast ExprMethodCall) {
        if !self.in_function {
            syn::visit::visit_expr_method_call(self, call);
            return;
        }

        let method = call.method.to_string();

        // Flag wrapping_* and saturating_* operations on financial values
        if method.starts_with("wrapping_") || method.starts_with("saturating_") {
            let expr_str = call.to_token_stream().to_string();

            // Check if this involves balance/amount/token related variables
            let is_financial = expr_str.contains("balance")
                || expr_str.contains("amount")
                || expr_str.contains("deposit")
                || expr_str.contains("stake")
                || expr_str.contains("token")
                || expr_str.contains("reward");

            if is_financial {
                let line = span_to_line(&call.method.span());
                self.findings.push(Finding {
                    detector_id: "NEAR-005".to_string(),
                    name: "near-wrapping-arithmetic".to_string(),
                    severity: Severity::Critical,
                    confidence: Confidence::Medium,
                    message: format!(
                        "{}() used on financial value - may silently lose precision",
                        method
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&call.method.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Use checked_* arithmetic and handle overflow explicitly for financial calculations".to_string(),
                    chain: Chain::Near,
                });
            }
        }

        syn::visit::visit_expr_method_call(self, call);
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
        IntegerOverflowDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_wrapping_on_balance() {
        let source = r#"
            use near_sdk::env;
            fn update_balance(&mut self, amount: u128) {
                self.balance = self.balance.wrapping_add(amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect wrapping_add on balance"
        );
    }

    #[test]
    fn test_no_finding_checked() {
        let source = r#"
            use near_sdk::env;
            fn update_balance(&mut self, amount: u128) -> Option<u128> {
                self.balance.checked_add(amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag checked_add");
    }

    #[test]
    fn test_no_finding_in_cfg_test_module() {
        // FP idx 4: wrapping_add inside a #[cfg(test)] module is test-only
        // code (compiled out of the deployed WASM) that intentionally
        // exercises the overflow edge case. It must not be flagged.
        let source = r#"
            use near_sdk::env;

            #[cfg(test)]
            mod tests {
                #[test]
                fn balance_wraps_at_u128_max_is_rejected() {
                    let balance: u128 = u128::MAX;
                    let wrapped = balance.wrapping_add(1);
                    assert_eq!(wrapped, 0);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag wrapping_add inside #[cfg(test)] module"
        );
    }

    #[test]
    fn test_no_finding_in_test_fn() {
        // A #[test] function not wrapped in a #[cfg(test)] module is still
        // test-only code and must not be flagged.
        let source = r#"
            use near_sdk::env;

            #[test]
            fn balance_overflow_case() {
                let balance: u128 = u128::MAX;
                let _ = balance.wrapping_add(1);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag wrapping_add inside a #[test] fn"
        );
    }
}
