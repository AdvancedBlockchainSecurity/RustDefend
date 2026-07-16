use quote::ToTokens;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{
    BinOp, Block, Expr, ExprBinary, ExprIf, ExprMethodCall, ExprPath, ImplItemFn, Lit, Local,
    Macro, Pat, Stmt, Token,
};

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

/// Strips parentheses/grouping so operand inspection sees through `(x)`.
fn strip_expr(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(p) => strip_expr(&p.expr),
        Expr::Group(g) => strip_expr(&g.expr),
        _ => expr,
    }
}

/// True for the relational operators that can compare a balance against zero.
fn is_comparison_op(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq(_) | BinOp::Ne(_) | BinOp::Lt(_) | BinOp::Gt(_) | BinOp::Le(_) | BinOp::Ge(_)
    )
}

/// True for a literal `0` in any suffixed form (`0`, `0u128`, ...).
fn is_zero_literal(expr: &Expr) -> bool {
    match strip_expr(expr) {
        Expr::Lit(lit) => match &lit.lit {
            Lit::Int(int) => int.base10_digits() == "0",
            _ => false,
        },
        _ => false,
    }
}

/// True for a `transferred_value()` accessor call, matched structurally as a
/// zero-argument method call rather than by name substring, so that
/// `transferred_value_total` and string literals cannot match.
fn is_transferred_value_call(expr: &Expr) -> bool {
    match strip_expr(expr) {
        Expr::MethodCall(call) => call.method == "transferred_value" && call.args.is_empty(),
        _ => false,
    }
}

/// True for macros that reject the call outright: an `assert!`-style condition
/// or an unconditional panic. Only the *first* argument of these is a
/// condition; the rest are formatting arguments.
fn is_reject_macro(mac: &Macro) -> bool {
    mac.path.segments.last().is_some_and(|seg| {
        matches!(
            seg.ident.to_string().as_str(),
            "assert" | "debug_assert" | "require" | "ensure" | "panic" | "unreachable" | "abort"
        )
    })
}

/// True when `expr` rejects the call: it returns/evaluates to an `Err(..)`, or
/// it panics.
fn expr_rejects(expr: &Expr) -> bool {
    match strip_expr(expr) {
        // `return Err(..)` / bare `return` inside a rejecting arm.
        Expr::Return(ret) => ret.expr.as_deref().is_some_and(expr_rejects),
        // A tail or returned `Err(..)` construction.
        Expr::Call(call) => match strip_expr(&call.func) {
            Expr::Path(path) => path
                .path
                .segments
                .last()
                .is_some_and(|seg| seg.ident == "Err"),
            _ => false,
        },
        Expr::Try(try_expr) => expr_rejects(&try_expr.expr),
        Expr::Macro(mac) => is_reject_macro(&mac.mac),
        _ => false,
    }
}

/// True when `block` rejects the call on entry -- i.e. it is the body of a
/// defensive guard rather than an ordinary branch. This is what separates
/// `if transferred_value() > 0 { return Err(..) }` (reject any value) from
/// `if transferred_value() == 0 { .. }` used as a precondition on a branch
/// that goes on to credit the deposit anyway.
fn block_rejects(block: &Block) -> bool {
    block.stmts.iter().any(|stmt| match stmt {
        Stmt::Expr(expr, _) => expr_rejects(expr),
        Stmt::Macro(mac) => is_reject_macro(&mac.mac),
        _ => false,
    })
}

/// Classifies every *use* of the transferred value inside a message body as
/// either a "guard" use (the value is compared against zero purely to reject
/// the call) or a "consumption" use (the value is read for its amount: bound,
/// credited, accumulated, passed on, ...).
///
/// This is the structural replacement for the old whole-body substring test,
/// which asked only whether a zero-comparison and the word `Err` both appeared
/// *somewhere*. That question is not the same as "is the value only rejected":
/// a require-nonzero precondition on a genuine deposit
/// (`if transferred_value() == 0 { return Err(..) } ... balance += value`)
/// answers yes to it while still consuming the deposit. Asking instead whether
/// any use consumes the value keeps such deposits flagged.
struct ValueUseVisitor {
    /// Locals bound directly to the transferred value, e.g.
    /// `let value = self.env().transferred_value();`. Reads of these count as
    /// reads of the call itself, so a guard written against the binding
    /// (`let v = ..transferred_value(); if v > 0 { return Err(..) }`) is still
    /// recognised as a guard.
    aliases: Vec<String>,
    /// Set while visiting the condition of a construct whose taken branch
    /// rejects the call.
    in_reject_cond: bool,
    guard_uses: usize,
    consumption_uses: usize,
}

impl ValueUseVisitor {
    fn new() -> Self {
        Self {
            aliases: Vec::new(),
            in_reject_cond: false,
            guard_uses: 0,
            consumption_uses: 0,
        }
    }

    /// True when `expr` evaluates to the transferred value: either the
    /// accessor call itself or a read of a local bound directly to it.
    fn is_value_expr(&self, expr: &Expr) -> bool {
        match strip_expr(expr) {
            Expr::Path(path) => path
                .path
                .get_ident()
                .is_some_and(|ident| self.aliases.contains(&ident.to_string())),
            _ => is_transferred_value_call(expr),
        }
    }
}

impl<'ast> Visit<'ast> for ValueUseVisitor {
    fn visit_local(&mut self, local: &'ast Local) {
        // `let value = self.env().transferred_value();` -- binding alone is not
        // a use. Record the alias and skip the initialiser so it is not counted
        // as consumption; how the binding is later *read* decides the verdict.
        if let Some(init) = &local.init {
            if init.diverge.is_none() && self.is_value_expr(&init.expr) {
                let pat = match &local.pat {
                    Pat::Type(pat_type) => &*pat_type.pat,
                    other => other,
                };
                if let Pat::Ident(pat_ident) = pat {
                    self.aliases.push(pat_ident.ident.to_string());
                    return;
                }
            }
        }
        syn::visit::visit_local(self, local);
    }

    fn visit_expr_if(&mut self, node: &'ast ExprIf) {
        // A zero-comparison in the condition of an `if` whose taken branch
        // rejects the call is a guard; the same comparison guarding a branch
        // that falls through into deposit logic is not.
        let rejects = block_rejects(&node.then_branch);
        let previous = self.in_reject_cond;
        self.in_reject_cond = rejects;
        self.visit_expr(&node.cond);
        self.in_reject_cond = previous;

        self.visit_block(&node.then_branch);
        if let Some((_, else_branch)) = &node.else_branch {
            self.visit_expr(else_branch);
        }
    }

    fn visit_expr_binary(&mut self, node: &'ast ExprBinary) {
        if is_comparison_op(&node.op) {
            let compares_to_zero = (self.is_value_expr(&node.left) && is_zero_literal(&node.right))
                || (self.is_value_expr(&node.right) && is_zero_literal(&node.left));
            if compares_to_zero {
                if self.in_reject_cond {
                    self.guard_uses += 1;
                } else {
                    // A zero-comparison that does not reject -- the value is
                    // being branched on, not refused. Treat as a real read.
                    self.consumption_uses += 1;
                }
                // Both operands are accounted for; descending would
                // double-count the value as a consumption.
                return;
            }
        }
        syn::visit::visit_expr_binary(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        // Reached only outside a zero-comparison guard (those return above), so
        // the value is being read for its amount.
        if node.method == "transferred_value" && node.args.is_empty() {
            self.consumption_uses += 1;
        }
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_path(&mut self, node: &'ast ExprPath) {
        if let Some(ident) = node.path.get_ident() {
            if self.aliases.contains(&ident.to_string()) {
                self.consumption_uses += 1;
            }
        }
    }

    fn visit_macro(&mut self, node: &'ast Macro) {
        // syn does not descend into macro token streams, so parse the arguments
        // ourselves -- otherwise `assert!(transferred_value() == 0)` would be
        // invisible to the classification above.
        let Ok(args) = node.parse_body_with(Punctuated::<Expr, Token![,]>::parse_terminated) else {
            return;
        };
        if is_reject_macro(node) {
            // Only the first argument is a condition; the remaining arguments
            // are the formatting message, and interpolating the value into a
            // panic message is not consuming it.
            let previous = self.in_reject_cond;
            self.in_reject_cond = true;
            if let Some(cond) = args.first() {
                self.visit_expr(cond);
            }
            self.in_reject_cond = previous;
            return;
        }
        for arg in &args {
            self.visit_expr(arg);
        }
    }
}

/// Returns true when the body reads `transferred_value()` *only* to reject any
/// attached value (a defensive zero-value guard), rather than to consume it as
/// a deposit. This is a common defense-in-depth idiom on intentionally
/// non-payable messages, so recommending `payable` would be exactly backwards.
///
/// We skip only when there is at least one guard use and *no* use that reads
/// the value for its amount. Any deposit logic -- including a deposit fronted
/// by a require-nonzero precondition, which the previous substring test could
/// not distinguish from a reject guard -- has a consumption use and stays
/// flagged.
fn is_pure_zero_value_reject_guard(block: &Block) -> bool {
    let mut visitor = ValueUseVisitor::new();
    visitor.visit_block(block);
    visitor.consumption_uses == 0 && visitor.guard_uses > 0
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
        // solely to reject attached value. Checked structurally against the
        // body AST: a body that also *consumes* the value is still flagged.
        if is_pure_zero_value_reject_guard(&method.block) {
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

    // MUST STILL FLAG: a require-nonzero precondition (`== 0` -> `Err`) fronting
    // a genuine deposit is NOT a reject guard -- the body goes on to credit the
    // attached value. The zero-comparison + `Err` pair matches the old
    // substring skip heuristic verbatim, which silenced this real vulnerability.
    #[test]
    fn test_still_flags_deposit_behind_require_nonzero_precondition() {
        let source = r#"
            impl Vault {
                #[ink(message)]
                pub fn deposit(&mut self) -> Result<(), Error> {
                    let value = self.env().transferred_value();
                    if self.env().transferred_value() == 0 {
                        return Err(Error::ZeroDeposit);
                    }
                    let caller = self.env().caller();
                    let prev = self.balances.get(&caller).copied().unwrap_or(0);
                    self.balances.insert(caller, prev + value);
                    self.total_deposited += value;
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Must flag a non-payable message that credits transferred_value(), even when a \
             require-nonzero precondition compares it against zero and returns Err"
        );
        assert_eq!(findings[0].detector_id, "INK-010");
    }

    // MUST STILL FLAG: the same require-nonzero precondition written against a
    // local bound to the value. Rejecting on the binding must not launder the
    // consumption that follows.
    #[test]
    fn test_still_flags_deposit_when_precondition_uses_bound_local() {
        let source = r#"
            impl Vault {
                #[ink(message)]
                pub fn deposit(&mut self) -> Result<(), Error> {
                    let value = self.env().transferred_value();
                    if value == 0 {
                        return Err(Error::ZeroDeposit);
                    }
                    self.balance += value;
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Must flag a deposit whose require-nonzero precondition reads a bound local"
        );
    }

    // A reject guard written against a local bound to the value is still a
    // reject guard: the binding is never read for its amount.
    #[test]
    fn test_no_finding_zero_value_reject_guard_via_bound_local() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn set_config(&mut self, v: u32) -> Result<(), Error> {
                    let attached = self.env().transferred_value();
                    if attached > 0 {
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
            "Should not flag a reject guard that compares a bound local against zero"
        );
    }

    // An assert!-style reject guard is equivalent to if-return-Err and was
    // skipped by the old heuristic too; keep skipping it.
    #[test]
    fn test_no_finding_zero_value_reject_guard_via_assert() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn set_config(&mut self, v: u32) {
                    assert!(self.env().transferred_value() == 0, "no value accepted");
                    self.config = v;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a message that asserts transferred_value() is zero"
        );
    }
}
