use quote::ToTokens;
use syn::visit::Visit;
use syn::{Pat, Stmt};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct ErrorHandlingDetector;

impl Detector for ErrorHandlingDetector {
    fn id(&self) -> &'static str {
        "INK-008"
    }
    fn name(&self) -> &'static str {
        "ink-result-suppression"
    }
    fn description(&self) -> &'static str {
        "Detects `let _ = expr` where expr returns Result (error suppression)"
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
        // Require ink!-specific source markers to avoid cross-chain FPs
        if !ctx.source.contains("#[ink(")
            && !ctx.source.contains("#[ink::")
            && !ctx.source.contains("ink_storage")
            && !ctx.source.contains("ink_env")
            && !ctx.source.contains("ink_lang")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = ErrorVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Collects every real identifier (path segments, method names, etc.) reachable
/// from an expression. Used to match danger keywords as *whole identifiers*
/// rather than raw substrings, so `caller` no longer matches `call`,
/// `transferred_value` no longer matches `transfer`, and `sender`/`spender` no
/// longer match `send`. String-literal contents are `LitStr`, not `Ident`, so
/// they are correctly excluded.
struct IdentCollector {
    idents: Vec<String>,
}

impl<'ast> Visit<'ast> for IdentCollector {
    fn visit_ident(&mut self, id: &'ast syn::Ident) {
        self.idents.push(id.to_string());
    }
}

/// True when the expression invokes something that plausibly returns a Result
/// worth handling. Keyword matching is identifier-exact to avoid substring FPs.
fn expr_has_result_keyword(expr: &syn::Expr) -> bool {
    let mut collector = IdentCollector { idents: Vec::new() };
    collector.visit_expr(expr);
    collector.idents.iter().any(|id| {
        matches!(
            id.as_str(),
            "send" | "transfer" | "invoke" | "call" | "execute" | "save" | "write"
        ) || id.starts_with("try_")
    })
}

/// True when the discarded initializer already handles the error, so nothing is
/// actually suppressed:
///   * `expr?`            — the Err variant is propagated to the caller.
///   * `expr.expect(..)`  — panics on Err (in ink! this traps and reverts).
///   * `expr.unwrap()`    — panics on Err (fail-loud).
///   * `expr.expect_err`/`unwrap_err` — panic on Ok (the error is consumed).
/// Note: `unwrap_or*` / `map_or*` are deliberately NOT treated as handled — they
/// silently substitute a fallback and genuinely swallow the error, which is a
/// real suppression we must keep flagging.
fn is_error_handled_expr(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Try(_) => true,
        syn::Expr::MethodCall(mc) => matches!(
            mc.method.to_string().as_str(),
            "expect" | "unwrap" | "expect_err" | "unwrap_err"
        ),
        _ => false,
    }
}

/// True when a function carries a unit/integration-test attribute. Discarding a
/// Result in a test is a deliberate pattern (a following assertion verifies the
/// observable effect) and the code is never compiled into the deployed Wasm.
fn is_test_fn(attrs: &[syn::Attribute]) -> bool {
    has_attribute(attrs, "test")
        || has_attribute(attrs, "ink::test")
        || has_attribute(attrs, "ink_e2e::test")
        || has_attribute(attrs, "tokio::test")
        || has_attribute(attrs, "async_std::test")
}

struct ErrorVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for ErrorVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        // Skip `#[cfg(test)]` modules entirely — test code is not deployed.
        if has_nested_attribute(&node.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        // Skip test functions (`#[test]`, `#[ink::test]`, `#[ink_e2e::test]`, ...).
        if is_test_fn(&node.attrs) {
            return;
        }
        syn::visit::visit_item_fn(self, node);
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        if let Stmt::Local(local) = stmt {
            if let Pat::Wild(_) = &local.pat {
                if let Some(init) = &local.init {
                    let expr_str = init.expr.to_token_stream().to_string();

                    // The error is already handled (`?`, `.expect()`, `.unwrap()`,
                    // `.expect_err()`, `.unwrap_err()`) — nothing is suppressed.
                    if is_error_handled_expr(&init.expr) {
                        syn::visit::visit_stmt(self, stmt);
                        return;
                    }

                    // Heuristic: check if expression likely returns Result, matching
                    // danger keywords as whole identifiers (not substrings).
                    let likely_result = expr_has_result_keyword(&init.expr);

                    // Skip common non-Result patterns that match above heuristics.
                    let is_false_positive = expr_str.contains("callback")
                        || expr_str.contains("channel")
                        || expr_str.contains("to_string")
                        || expr_str.contains("writeln")
                        || expr_str.contains("write !")
                        || expr_str.contains("write!")
                        || expr_str.contains("println")
                        || expr_str.contains("eprintln")
                        // Skip if the assignment is used for signaling (e.g., let _ = tx.send())
                        // which is an intentional pattern
                        || expr_str.contains("tx .")
                        || expr_str.contains("sender .");

                    if likely_result && !is_false_positive {
                        let line = span_to_line(&local.let_token.span);
                        self.findings.push(Finding {
                            detector_id: "INK-008".to_string(),
                            name: "ink-result-suppression".to_string(),
                            severity: Severity::Medium,
                            confidence: Confidence::Medium,
                            message: format!(
                                "Result of '{}' is discarded with `let _ = ...`",
                                truncate_str(&expr_str, 60)
                            ),
                            file: self.ctx.file_path.clone(),
                            line,
                            column: 1,
                            snippet: snippet_at_line(&self.ctx.source, line),
                            recommendation: "Handle the Result with `?` operator or explicit error handling instead of discarding it".to_string(),
                            chain: Chain::Ink,
                        });
                    }
                }
            }
        }

        syn::visit::visit_stmt(self, stmt);
    }
}

fn truncate_str(s: &str, max_len: usize) -> String {
    if s.len() <= max_len {
        s.to_string()
    } else {
        format!("{}...", &s[..max_len])
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
        ErrorHandlingDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_suppressed_result() {
        let source = r#"
            #[ink(message)]
            fn send_tokens(&mut self) {
                let _ = self.env().transfer(dest, amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect suppressed Result");
    }

    #[test]
    fn test_no_finding_handled() {
        let source = r#"
            fn send_tokens(&mut self) -> Result<(), Error> {
                self.env().transfer(dest, amount)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag properly handled Result"
        );
    }

    // FP idx 0: `call` substring must not match the identifier `caller`, and
    // `transfer` must not match `transferred_value`. Mapping::insert returns an
    // Option, not a Result.
    #[test]
    fn test_no_finding_caller_identifier_insert() {
        let source = r#"
            #[ink(message)]
            pub fn deposit(&mut self) {
                let caller = self.env().caller();
                let _ = self.balances.insert(caller, &self.env().transferred_value());
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag Mapping::insert with a `caller` argument"
        );
    }

    // FP idx 1: `let _ = expr?;` — the `?` already propagates the error.
    #[test]
    fn test_no_finding_try_propagation() {
        let source = r#"
            #[ink(message)]
            pub fn withdraw(&mut self) -> Result<(), Error> {
                let _ = self.do_transfer(to, amount)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a `?`-propagated expression"
        );
    }

    // FP idx 2: `send` substring must not match `sender`/`spender` used as
    // arguments to Mapping::insert.
    #[test]
    fn test_no_finding_sender_identifier_insert() {
        let source = r#"
            #[ink(message)]
            pub fn approve(&mut self) {
                let sender = self.env().caller();
                let _ = self.allowances.insert((sender, spender), &amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag Mapping::insert with `sender`/`spender` arguments"
        );
    }

    // FP idx 3: statements inside `#[cfg(test)]` / `#[ink::test]` code must be
    // ignored.
    #[test]
    fn test_no_finding_inside_test_module() {
        let source = r#"
            #[ink::contract]
            mod token {
                #[cfg(test)]
                mod tests {
                    use super::*;
                    #[ink::test]
                    fn transfer_to_zero_fails_silently_is_ok() {
                        let mut c = Token::new(100);
                        let _ = c.transfer(zero, 10);
                        assert_eq!(c.balance_of(zero), 0);
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag discards inside #[cfg(test)] / #[ink::test] code"
        );
    }

    // FP idx 4: a terminal `.expect(..)` consumes the Result (panics on Err),
    // so the error is handled, not suppressed.
    #[test]
    fn test_no_finding_terminal_expect() {
        let source = r#"
            #[ink(message)]
            pub fn payout(&mut self) {
                let _ = self.env().transfer(to, amount).expect("payout transfer failed");
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a Result consumed by `.expect()`"
        );
    }
}
