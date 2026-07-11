use quote::ToTokens;
use syn::visit::Visit;
use syn::ImplItemFn;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingPayableCheckDetector;

impl Detector for MissingPayableCheckDetector {
    fn id(&self) -> &'static str {
        "INK-010"
    }
    fn name(&self) -> &'static str {
        "ink-missing-payable-check"
    }
    fn description(&self) -> &'static str {
        "Detects non-payable #[ink(message)] methods that reference transferred_value()"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Ink
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = PayableVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct PayableVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// Returns true when the body reads `transferred_value()` only to reject any
/// attached value (a defensive zero-value guard), rather than to consume it as
/// a deposit. This is a common defense-in-depth idiom on intentionally
/// non-payable messages, so recommending `payable` would be exactly backwards.
///
/// We require BOTH a comparison of the call result against zero AND an
/// error/assert/panic keyword in the body. Genuine deposit logic
/// (`self.balance += self.env().transferred_value()`) contains no
/// comparison-to-zero and therefore remains flagged.
fn is_zero_value_reject_guard(body_src: &str) -> bool {
    let has_zero_comparison = body_src.contains("transferred_value () == 0")
        || body_src.contains("transferred_value () != 0")
        || body_src.contains("transferred_value () > 0")
        || body_src.contains("transferred_value () < 0")
        || body_src.contains("transferred_value () >= 0")
        || body_src.contains("transferred_value () <= 0");
    let has_reject = body_src.contains("Err")
        || body_src.contains("assert")
        || body_src.contains("panic")
        || body_src.contains("revert");
    has_zero_comparison && has_reject
}

impl<'ast, 'a> Visit<'ast> for PayableVisitor<'a> {
    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        // Check for #[ink(message)] / #[ink(payable)] attributes.
        //
        // We match the attribute *path* structurally (`ink`) before substring
        // matching its arguments, so that doc comments (path `doc`) whose free
        // text happens to contain the words "ink" and "message" are not
        // mistaken for a message attribute.
        //
        // `payable` is tracked independently of `message` because ink! allows
        // splitting arguments across attributes: `#[ink(message)]
        // #[ink(payable)]` is exactly equivalent to `#[ink(message, payable)]`.
        let mut has_ink_message = false;
        let mut is_payable = false;
        for attr in &method.attrs {
            if !attr.path().is_ident("ink") {
                continue;
            }
            let tokens = attr.meta.to_token_stream().to_string();
            if tokens.contains("message") {
                has_ink_message = true;
            }
            if tokens.contains("payable") {
                is_payable = true;
            }
        }

        if !has_ink_message || is_payable {
            return;
        }

        let body_src = method.block.to_token_stream().to_string();

        // Match the actual accessor *call* `transferred_value ()` (syn renders
        // a space before the parens) rather than the bare word. This avoids
        // over-matching identifiers such as `transferred_value_total` (which
        // render without a following `()`) and text inside string literals.
        if !body_src.contains("transferred_value ()") {
            return;
        }

        // Skip intentionally non-payable messages that read transferred_value()
        // solely to reject attached value.
        if is_zero_value_reject_guard(&body_src) {
            return;
        }

        let fn_name = method.sig.ident.to_string();
        let line = span_to_line(&method.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "INK-010".to_string(),
            name: "ink-missing-payable-check".to_string(),
            severity: Severity::Medium,
            confidence: Confidence::Medium,
            message: format!(
                "#[ink(message)] '{}' uses transferred_value() but is not marked payable",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&method.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add `payable` to the ink attribute: `#[ink(message, payable)]` if the method should accept value transfers".to_string(),
            chain: Chain::Ink,
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
            Chain::Ink,
            std::collections::HashMap::new(),
        );
        MissingPayableCheckDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_non_payable_with_transferred_value() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn deposit(&mut self) {
                    let value = self.env().transferred_value();
                    self.balance += value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect non-payable using transferred_value"
        );
    }

    #[test]
    fn test_no_finding_payable_method() {
        let source = r#"
            impl MyContract {
                #[ink(message, payable)]
                pub fn deposit(&mut self) {
                    let value = self.env().transferred_value();
                    self.balance += value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag payable method");
    }

    // FP idx 0: payable declared in a separate #[ink(payable)] attribute is
    // equivalent to #[ink(message, payable)] and must not be flagged.
    #[test]
    fn test_no_finding_split_payable_attribute() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                #[ink(payable)]
                pub fn deposit(&mut self) {
                    let value = self.env().transferred_value();
                    self.balance += value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a method made payable via a separate #[ink(payable)] attribute"
        );
    }

    // FP idx 1: a doc comment mentioning "ink message" on a plain private
    // helper (no #[ink(message)] attribute) must not be treated as a message.
    #[test]
    fn test_no_finding_doc_comment_mentions_ink_message() {
        let source = r#"
            impl MyContract {
                /// Internal helper for the ink message `deposit`.
                fn credit_caller(&mut self) {
                    let value = self.env().transferred_value();
                    self.balance += value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a private helper whose doc comment mentions 'ink message'"
        );
    }

    // FP idx 2: an identifier that contains `transferred_value` as a substring
    // (with no actual env().transferred_value() call) must not be flagged.
    #[test]
    fn test_no_finding_transferred_value_substring_identifier() {
        let source = r#"
            impl MyToken {
                #[ink(message)]
                pub fn transfer(&mut self, to: AccountId, amount: Balance) {
                    let transferred_value_total = self.total_transferred.saturating_add(amount);
                    self.total_transferred = transferred_value_total;
                    self.balances.insert(to, amount);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag an identifier that merely contains 'transferred_value'"
        );
    }

    // FP idx 3: a defensive zero-value reject guard on an intentionally
    // non-payable message must not be flagged.
    #[test]
    fn test_no_finding_zero_value_reject_guard() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn set_config(&mut self, v: u32) -> Result<(), Error> {
                    if self.env().transferred_value() > 0 {
                        return Err(Error::NoValueAccepted);
                    }
                    self.config = v;
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a message that reads transferred_value() only to reject it"
        );
    }
}
