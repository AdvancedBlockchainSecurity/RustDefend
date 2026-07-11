use std::collections::HashSet;

use proc_macro2::Span;
use quote::ToTokens;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{
    Attribute, BinOp, Expr, ExprBinary, ExprCall, ExprIf, ExprMacro, ExprMatch, ExprMethodCall,
    ExprWhile, ImplItemFn, ItemFn, ItemMod, Macro, StmtMacro,
};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::{snippet_at_line, span_to_column, span_to_line};

pub struct TimestampDependenceDetector;

impl Detector for TimestampDependenceDetector {
    fn id(&self) -> &'static str {
        "INK-004"
    }
    fn name(&self) -> &'static str {
        "ink-timestamp-dependence"
    }
    fn description(&self) -> &'static str {
        "Detects block_timestamp() usage in decision logic"
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
        let mut flagged: HashSet<(usize, usize)> = HashSet::new();
        let mut visitor = DecisionVisitor {
            findings: &mut findings,
            ctx,
            flagged: &mut flagged,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Walks the parsed AST and flags every `block_timestamp()` call that participates
/// in decision logic — i.e. it appears (possibly nested) as an operand of a
/// comparison/arithmetic expression, or inside an `if` / `match` / `while`
/// condition, or inside a guard macro such as `assert!`/`ensure!`/`require!`.
///
/// Operating on the AST (instead of raw `str::contains`) is what eliminates the
/// historical false positives:
///   * the substring "if" inside identifiers like `verified_at`/`modified` no
///     longer counts as an if-expression (FP idx 0),
///   * the `->` return arrow and generic `<...>` brackets in a one-line getter
///     are tokens, never binary operators (FP idx 1),
///   * line comments / doc comments never appear in the token stream (FP idx 2),
///   * `#[cfg(test)]` modules and `#[ink::test]`/`#[test]` functions are pruned
///     before their bodies are inspected (FP idx 3).
///
/// A pure record-keeping store (`self.created_at = self.env().block_timestamp();`)
/// or a read-only accessor is an assignment / bare call with no decision node, so
/// it is correctly left unflagged — while real comparisons and timestamp
/// arithmetic (including inside macros) are still detected.
struct DecisionVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    /// De-duplicates findings by (line, column) of the `block_timestamp` call,
    /// since a single call can be reached through several decision nodes
    /// (e.g. an `if` whose condition is itself a comparison).
    flagged: &'a mut HashSet<(usize, usize)>,
}

impl<'ast, 'a> Visit<'ast> for DecisionVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Never scan `#[cfg(test)]` modules — test code is not a deployment target.
        if has_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (#[test] / #[ink::test] / #[tokio::test]) and any
        // fn gated behind #[cfg(test)].
        if is_test_fn(&func.attrs) || has_cfg_test(&func.attrs) {
            return;
        }
        syn::visit::visit_item_fn(self, func);
    }

    fn visit_impl_item_fn(&mut self, func: &'ast ImplItemFn) {
        // ink! messages live in `impl` blocks; skip test methods here too.
        if is_test_fn(&func.attrs) || has_cfg_test(&func.attrs) {
            return;
        }
        syn::visit::visit_impl_item_fn(self, func);
    }

    fn visit_expr_binary(&mut self, expr: &'ast ExprBinary) {
        if is_decision_op(&expr.op) {
            self.flag_timestamps_in(&expr.left);
            self.flag_timestamps_in(&expr.right);
        }
        syn::visit::visit_expr_binary(self, expr);
    }

    fn visit_expr_if(&mut self, expr: &'ast ExprIf) {
        // A `block_timestamp()` anywhere in the branch condition drives control
        // flow — even when it is passed to a helper rather than compared inline.
        self.flag_timestamps_in(&expr.cond);
        syn::visit::visit_expr_if(self, expr);
    }

    fn visit_expr_match(&mut self, expr: &'ast ExprMatch) {
        self.flag_timestamps_in(&expr.expr);
        syn::visit::visit_expr_match(self, expr);
    }

    fn visit_expr_while(&mut self, expr: &'ast ExprWhile) {
        self.flag_timestamps_in(&expr.cond);
        syn::visit::visit_expr_while(self, expr);
    }

    fn visit_expr_macro(&mut self, expr: &'ast ExprMacro) {
        // Guard macros (assert!/ensure!/require!/debug_assert!) embed a real
        // comparison in their token stream; parse it back to exprs so timestamp
        // comparisons inside them are not missed. Spans are preserved.
        self.handle_macro(&expr.mac);
    }

    fn visit_stmt_macro(&mut self, stmt: &'ast StmtMacro) {
        self.handle_macro(&stmt.mac);
    }
}

impl<'a> DecisionVisitor<'a> {
    /// Record a finding for each `block_timestamp()` call found anywhere inside
    /// `expr` (the decision-relevant sub-tree), de-duplicated by source location.
    fn flag_timestamps_in(&mut self, expr: &Expr) {
        let mut spans = Vec::new();
        collect_block_timestamp_spans(expr, &mut spans);
        for span in spans {
            let line = span_to_line(&span);
            let column = span_to_column(&span);
            if !self.flagged.insert((line, column)) {
                continue;
            }
            let snippet = snippet_at_line(&self.ctx.source, line);
            self.findings.push(Finding {
                detector_id: "INK-004".to_string(),
                name: "ink-timestamp-dependence".to_string(),
                severity: Severity::Medium,
                confidence: Confidence::Medium,
                message: "block_timestamp() used in decision logic - can be manipulated by validators".to_string(),
                file: self.ctx.file_path.clone(),
                line,
                column,
                snippet,
                recommendation: "Block timestamps can be slightly manipulated by validators. Use block_number() for ordering, or add tolerance margins for time-based logic".to_string(),
                chain: Chain::Ink,
            });
        }
    }

    /// Parse a macro body as a comma-separated list of expressions and run the
    /// same decision analysis over them, preserving original spans. This keeps
    /// parity with the previous line-based scan for `block_timestamp` inside
    /// macros (avoiding a false negative) without re-introducing comment/`->`
    /// false positives, since macro token streams contain neither.
    fn handle_macro(&mut self, mac: &Macro) {
        let parsed = mac.parse_body_with(Punctuated::<Expr, syn::Token![,]>::parse_terminated);
        if let Ok(exprs) = parsed {
            let mut child = DecisionVisitor {
                findings: &mut *self.findings,
                ctx: self.ctx,
                flagged: &mut *self.flagged,
            };
            for e in &exprs {
                child.visit_expr(e);
            }
        }
    }
}

/// True if the binary operator represents a comparison or arithmetic operation
/// (the operations through which a manipulable timestamp can influence a result).
fn is_decision_op(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Lt(_)
            | BinOp::Gt(_)
            | BinOp::Le(_)
            | BinOp::Ge(_)
            | BinOp::Eq(_)
            | BinOp::Ne(_)
            | BinOp::Add(_)
            | BinOp::Sub(_)
            | BinOp::Mul(_)
            | BinOp::Div(_)
            | BinOp::Rem(_)
            | BinOp::AddAssign(_)
            | BinOp::SubAssign(_)
            | BinOp::MulAssign(_)
            | BinOp::DivAssign(_)
            | BinOp::RemAssign(_)
    )
}

/// Collect the spans of every `block_timestamp` call inside `expr`, covering both
/// the method-call form (`self.env().block_timestamp()`) and the free-function
/// form (`ink_env::block_timestamp::<E>()`).
fn collect_block_timestamp_spans(expr: &Expr, out: &mut Vec<Span>) {
    struct Collector<'b> {
        out: &'b mut Vec<Span>,
    }
    impl<'ast, 'b> Visit<'ast> for Collector<'b> {
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            if node.method == "block_timestamp" {
                self.out.push(node.method.span());
            }
            syn::visit::visit_expr_method_call(self, node);
        }
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Expr::Path(p) = &*node.func {
                if let Some(seg) = p.path.segments.last() {
                    if seg.ident == "block_timestamp" {
                        self.out.push(seg.ident.span());
                    }
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }
    let mut c = Collector { out };
    c.visit_expr(expr);
}

/// True if the attribute list marks a test function
/// (#[test] / #[ink::test] / #[tokio::test]).
fn is_test_fn(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| {
        a.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

/// True if the attribute list contains `#[cfg(test)]`.
fn has_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| {
        if a.path().is_ident("cfg") {
            a.meta.to_token_stream().to_string().contains("test")
        } else {
            false
        }
    })
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
        TimestampDependenceDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_timestamp_comparison() {
        let source = r#"
            #[ink(message)]
            fn is_expired(&self) -> bool {
                self.env().block_timestamp() > self.deadline
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect timestamp in comparison"
        );
    }

    #[test]
    fn test_no_finding_timestamp_logging() {
        let source = r#"
            #[ink(message)]
            fn get_timestamp(&self) -> u64 {
                self.env().block_timestamp()
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag simple timestamp read");
    }

    // Timestamp arithmetic (elapsed-time computation) must still be flagged.
    #[test]
    fn test_detects_timestamp_arithmetic() {
        let source = r#"
            #[ink(message)]
            fn elapsed(&self) -> u64 {
                self.env().block_timestamp() - self.start
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect timestamp arithmetic, got: {:?}",
            findings
        );
    }

    // A comparison hidden inside a guard macro must still be flagged (no false
    // negative from macro token streams not being expressions by default).
    #[test]
    fn test_detects_timestamp_in_assert_macro() {
        let source = r#"
            #[ink(message)]
            fn guard(&self) {
                assert!(self.env().block_timestamp() > self.deadline, "expired");
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect timestamp comparison inside assert!, got: {:?}",
            findings
        );
    }

    // FP idx 0: record-keeping assignment to a field whose name contains the
    // substring "if" ("verified_at") is a plain store, not decision logic.
    #[test]
    fn test_no_finding_record_keeping_if_substring() {
        let source = r#"
            #[ink(message)]
            pub fn verify(&mut self) {
                self.verified_at = self.env().block_timestamp();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag record-keeping store where 'if' is only a substring, got: {:?}",
            findings
        );
    }

    // FP idx 1: one-line getter whose `-> u64` return arrow contains '-' and '>'.
    #[test]
    fn test_no_finding_one_line_getter() {
        let source = r#"
            #[ink(message)]
            pub fn now(&self) -> u64 { self.env().block_timestamp() }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a read-only accessor whose signature has '->', got: {:?}",
            findings
        );
    }

    // FP idx 1 (variant): generic return type `Option<u64>` must not trigger the
    // '<'/'>' operator heuristic on a read-only getter.
    #[test]
    fn test_no_finding_getter_with_generic_return() {
        let source = r#"
            #[ink(message)]
            pub fn maybe_now(&self) -> Option<u64> { Some(self.env().block_timestamp()) }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a getter whose return type has angle brackets, got: {:?}",
            findings
        );
    }

    // FP idx 2: comments (line and trailing) mentioning block_timestamp or
    // containing '-' must never participate in detection.
    #[test]
    fn test_no_finding_comment_text() {
        let source = r#"
            #[ink(message)]
            pub fn record(&mut self) {
                // block_timestamp() is in milliseconds - not seconds
                self.created_at = self.env().block_timestamp(); // audit-trail only
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag comment text or a store with a trailing comment, got: {:?}",
            findings
        );
    }

    // FP idx 3: timestamp assertions inside #[cfg(test)] modules are off-chain
    // test code and must not be reported as on-chain vulnerabilities.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                #[ink::test]
                fn advances_time() {
                    ink::env::test::set_block_timestamp::<ink::env::DefaultEnvironment>(1000);
                    assert!(contract.env().block_timestamp() >= 1000);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag timestamp comparisons in #[cfg(test)] code, got: {:?}",
            findings
        );
    }
}
