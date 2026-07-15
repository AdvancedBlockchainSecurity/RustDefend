use quote::ToTokens;
use std::collections::HashSet;
use syn::visit::Visit;
use syn::{Expr, ExprMethodCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct CheckedArithmeticUnwrapDetector;

impl Detector for CheckedArithmeticUnwrapDetector {
    fn id(&self) -> &'static str {
        "SOL-020"
    }
    fn name(&self) -> &'static str {
        "checked-arithmetic-unwrap"
    }
    fn description(&self) -> &'static str {
        "Detects .checked_add/sub/mul/div(...).unwrap() chains that panic instead of propagating errors"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        if !ctx.source.contains("solana_program")
            && !ctx.source.contains("anchor_lang")
            && !ctx.source.contains("AccountInfo")
            && !ctx.source.contains("ProgramResult")
            && !ctx.source.contains("solana_sdk")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = CheckedUnwrapVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct CheckedUnwrapVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

const CHECKED_OPS: &[&str] = &[
    "checked_add",
    "checked_sub",
    "checked_mul",
    "checked_div",
    "checked_rem",
    "checked_pow",
    "checked_shl",
    "checked_shr",
];

fn is_checked_op(name: &str) -> bool {
    CHECKED_OPS.contains(&name)
}

/// If `expr` is directly a method call to a `checked_*` op, return that call.
fn checked_call(expr: &Expr) -> Option<&ExprMethodCall> {
    if let Expr::MethodCall(mc) = expr {
        if is_checked_op(&mc.method.to_string()) {
            return Some(mc);
        }
    }
    None
}

/// Collects the token-stream text of every `checked_*` expression that is
/// explicitly guarded by an `.is_none()` / `.is_some()` check (the classic
/// guard-then-unwrap idiom). Scoped to a single function body: it does NOT
/// descend into nested item fns or nested modules.
struct GuardFinder {
    guarded: HashSet<String>,
}

impl<'ast> Visit<'ast> for GuardFinder {
    fn visit_item_fn(&mut self, _f: &'ast ItemFn) {
        // Stop: nested fns are handled separately by the outer visitor.
    }
    fn visit_item_mod(&mut self, _m: &'ast ItemMod) {
        // Stop: nested modules are handled separately by the outer visitor.
    }
    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        let method = node.method.to_string();
        if method == "is_none" || method == "is_some" {
            if let Some(checked) = checked_call(&node.receiver) {
                self.guarded.insert(checked.to_token_stream().to_string());
            }
        }
        syn::visit::visit_expr_method_call(self, node);
    }
}

struct UnwrapHit {
    op: String,
    line: usize,
    column: usize,
    /// Token-stream text of the `checked_*` receiver expression.
    receiver_tokens: String,
}

/// Collects `.unwrap()` calls whose receiver is *directly* a `checked_*` call,
/// i.e. real `a.checked_add(b).unwrap()` chains. Scoped to a single function
/// body (does not descend into nested item fns or nested modules).
struct UnwrapFinder {
    hits: Vec<UnwrapHit>,
}

impl<'ast> Visit<'ast> for UnwrapFinder {
    fn visit_item_fn(&mut self, _f: &'ast ItemFn) {}
    fn visit_item_mod(&mut self, _m: &'ast ItemMod) {}
    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        if node.method == "unwrap" {
            if let Some(checked) = checked_call(&node.receiver) {
                self.hits.push(UnwrapHit {
                    op: checked.method.to_string(),
                    line: span_to_line(&checked.method.span()),
                    column: span_to_column(&checked.method.span()),
                    receiver_tokens: checked.to_token_stream().to_string(),
                });
            }
        }
        syn::visit::visit_expr_method_call(self, node);
    }
}

impl<'ast, 'a> Visit<'ast> for CheckedUnwrapVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Code under #[cfg(test)] is never compiled into the on-chain program;
        // unwrap in test fixtures/helpers is idiomatic and poses no runtime risk.
        if has_attribute_with_value(&module.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        if fn_name.contains("test") || has_attribute(&func.attrs, "test") {
            return;
        }

        // Collect checked expressions that are guarded by is_none()/is_some().
        let mut guards = GuardFinder {
            guarded: HashSet::new(),
        };
        guards.visit_block(&func.block);

        // Collect real checked_*(...).unwrap() chains in this function body only.
        let mut unwraps = UnwrapFinder { hits: Vec::new() };
        unwraps.visit_block(&func.block);

        // One finding per op per function (matches historical behavior).
        let mut reported: HashSet<String> = HashSet::new();
        for hit in unwraps.hits {
            // Suppress the guard-then-unwrap idiom: the exact same checked
            // expression was proven Some via an earlier is_none()/is_some()
            // guard with an early return, so the unwrap can never panic.
            if guards.guarded.contains(&hit.receiver_tokens) {
                continue;
            }
            if !reported.insert(hit.op.clone()) {
                continue;
            }

            self.findings.push(Finding {
                detector_id: "SOL-020".to_string(),
                name: "checked-arithmetic-unwrap".to_string(),
                severity: Severity::Medium,
                confidence: Confidence::High,
                message: format!(
                    "Function '{}' calls .{}().unwrap() — use .ok_or(...)? to propagate errors instead of panicking",
                    func.sig.ident, hit.op
                ),
                file: self.ctx.file_path.clone(),
                line: hit.line,
                column: hit.column,
                snippet: snippet_at_line(&self.ctx.source, hit.line),
                recommendation: format!(
                    "Replace .{}().unwrap() with .{}().ok_or(MyError::Overflow)? to return an error instead of panicking",
                    hit.op, hit.op
                ),
                chain: Chain::Solana,
            });
        }

        // Recurse to handle nested fns / nested modules with correct scoping.
        syn::visit::visit_item_fn(self, func);
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
            Chain::Solana,
            std::collections::HashMap::new(),
        );
        CheckedArithmeticUnwrapDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_checked_add_unwrap() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn calculate(a: u64, b: u64) -> u64 {
                a.checked_add(b).unwrap()
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect checked_add().unwrap()");
    }

    #[test]
    fn test_detects_checked_sub_unwrap() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn calculate(a: u64, b: u64) -> u64 {
                a.checked_sub(b).unwrap()
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect checked_sub().unwrap()");
    }

    #[test]
    fn test_no_finding_with_question_mark() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn calculate(a: u64, b: u64) -> Result<u64, ProgramError> {
                let result = a.checked_add(b).ok_or(ProgramError::ArithmeticOverflow)?;
                Ok(result)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag .checked_add(...).ok_or(...)?"
        );
    }

    #[test]
    fn test_no_finding_without_solana_markers() {
        let source = r#"
            fn calculate(a: u64, b: u64) -> u64 {
                a.checked_add(b).unwrap()
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag without Solana source markers"
        );
    }

    // ---- False-positive regression tests ----

    /// FP #0: guard-then-unwrap idiom. The overflow case is checked via
    /// `.is_none()` with an early Err return, so the identical second
    /// `checked_add(...).unwrap()` can never panic.
    #[test]
    fn test_no_finding_guard_then_unwrap() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn add(a: u64, b: u64) -> Result<u64, ProgramError> {
                if a.checked_add(b).is_none() {
                    return Err(ProgramError::ArithmeticOverflow);
                }
                let total = a.checked_add(b).unwrap();
                Ok(total)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag guard-then-unwrap idiom (is_none early return)"
        );
    }

    /// FP #1: checked op fully handled by a match; the nearby `.unwrap()` is on
    /// `Pubkey::from_str` of a compile-time constant, unrelated to arithmetic.
    #[test]
    fn test_no_finding_match_handled_unrelated_unwrap() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn distribute(a: u64, b: u64) -> Result<u64, ProgramError> {
                let total = match a.checked_add(b) {
                    Some(v) => v,
                    None => return Err(ProgramError::ArithmeticOverflow),
                };
                let admin = Pubkey::from_str("11111111111111111111111111111111").unwrap();
                Ok(total)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a match-handled checked op with an unrelated unwrap nearby"
        );
    }

    /// FP #2: helper fn inside a #[cfg(test)] module — never compiled on-chain.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            #[cfg(test)]
            mod tests {
                fn setup_supply(a: u64, b: u64) -> u64 {
                    a.checked_mul(b).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag unwrap inside a #[cfg(test)] module helper"
        );
    }

    /// FP #3: checked op handled by an if-let/else early return; the nearby
    /// `.unwrap()` is on `name.chars().next()`, unrelated to the arithmetic.
    #[test]
    fn test_no_finding_if_let_handled_unrelated_unwrap() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn settle(amount: u64, fee: u64, name: &str) -> Result<u64, ProgramError> {
                let net = if let Some(v) = amount.checked_sub(fee) {
                    v
                } else {
                    return Err(ProgramError::ArithmeticOverflow);
                };
                let first_char = name.chars().next().unwrap();
                let _ = first_char;
                Ok(net)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag an if-let-handled checked op with an unrelated unwrap nearby"
        );
    }

    /// FP #4: the only ".unwrap()" is text inside a msg! string literal in the
    /// overflow-handling arm — there is no unwrap call at all.
    #[test]
    fn test_no_finding_unwrap_in_string_literal() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn add(a: u64, b: u64) -> u64 {
                let total = match a.checked_add(b) {
                    Some(v) => v,
                    None => {
                        msg!("overflow: refusing to .unwrap() blindly");
                        return 0;
                    }
                };
                total
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag \".unwrap()\" text inside a string literal"
        );
    }
}
