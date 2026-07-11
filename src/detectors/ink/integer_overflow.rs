use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, BinOp, Expr, ExprBinary, FnArg, ItemFn, ItemMod, Lit, Local, Pat, Type};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct IntegerOverflowDetector;

impl Detector for IntegerOverflowDetector {
    fn id(&self) -> &'static str {
        "INK-002"
    }
    fn name(&self) -> &'static str {
        "ink-integer-overflow"
    }
    fn description(&self) -> &'static str {
        "Detects unchecked arithmetic on Balance/u128 types (cargo-contract enables overflow-checks by default)"
    }
    fn severity(&self) -> Severity {
        Severity::Low
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Ink
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Only fire on ink! contracts — check for ink-specific markers in source
        if !ctx.source.contains("#[ink(")
            && !ctx.source.contains("#[ink::")
            && !ctx.source.contains("ink_storage")
            && !ctx.source.contains("ink_env")
            && !ctx.source.contains("ink_lang")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = OverflowVisitor {
            findings: &mut findings,
            ctx,
            in_function: false,
            balance_idents: Vec::new(),
            body_normalized: String::new(),
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct OverflowVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    in_function: bool,
    /// Identifiers (params / typed let-bindings) whose declared type is Balance/u128.
    balance_idents: Vec<String>,
    /// Whitespace-stripped token source of the enclosing function body, used to
    /// detect a dominating comparison guard for subtractions.
    body_normalized: String,
}

impl<'ast, 'a> Visit<'ast> for OverflowVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Never scan `#[cfg(test)]` modules — test code is not a deployment target.
        if has_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (#[test] / #[ink::test] / #[tokio::test]).
        if is_test_fn(&func.attrs) {
            return;
        }

        // Collect operands that are provably Balance/u128 by declared type
        // (params + typed let-bindings). This intentionally ignores doc
        // comments and string literals, which never introduce a typed binding.
        let balance_idents = collect_balance_idents(func);

        // Gate on the function SIGNATURE only (not the stringified full item,
        // which serializes doc comments as `#[doc = "..."]` and inlines string
        // literals) — plus any Balance/u128-typed local binding. This preserves
        // detection for real Balance arithmetic while ignoring functions that
        // merely mention "Balance"/"u128" in documentation or messages.
        let sig_src = func.sig.to_token_stream().to_string();
        let sig_has_balance = sig_src.contains("Balance") || sig_src.contains("u128");

        if sig_has_balance || !balance_idents.is_empty() {
            let prev_in = self.in_function;
            let prev_ids = std::mem::take(&mut self.balance_idents);
            let prev_body = std::mem::take(&mut self.body_normalized);

            self.in_function = true;
            self.balance_idents = balance_idents;
            self.body_normalized = strip_ws(&fn_body_source(func));

            syn::visit::visit_item_fn(self, func);

            self.in_function = prev_in;
            self.balance_idents = prev_ids;
            self.body_normalized = prev_body;
        } else {
            // Recurse (e.g. for nested items) but do not flag arithmetic here.
            let prev_in = self.in_function;
            self.in_function = false;
            syn::visit::visit_item_fn(self, func);
            self.in_function = prev_in;
        }
    }

    fn visit_expr_binary(&mut self, expr: &'ast ExprBinary) {
        if !self.in_function {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        let is_arithmetic = matches!(
            expr.op,
            BinOp::Add(_)
                | BinOp::Sub(_)
                | BinOp::Mul(_)
                | BinOp::AddAssign(_)
                | BinOp::SubAssign(_)
                | BinOp::MulAssign(_)
        );

        if !is_arithmetic {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // Skip literal-only arithmetic (const folding, cannot depend on input).
        if matches!(&*expr.left, syn::Expr::Lit(_)) && matches!(&*expr.right, syn::Expr::Lit(_)) {
            return;
        }

        // FP4: `String + &str` (and other string concatenation) is not integer
        // arithmetic — there is no checked_/saturating_ variant and no overflow.
        if is_string_expr(&expr.left) || is_string_expr(&expr.right) {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // FP2: only flag when at least one operand is plausibly a Balance/u128
        // value. Index/counter math (usize) inside a Balance-gated function is
        // not the targeted vulnerability class.
        if !operand_is_balance_like(&expr.left, &self.balance_idents)
            && !operand_is_balance_like(&expr.right, &self.balance_idents)
        {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // FP1: guard-then-subtract. A subtraction dominated by an explicit
        // comparison guard on the same operands (assert!/ensure!/if a >= b)
        // cannot underflow. Only applies to Sub/SubAssign.
        if matches!(expr.op, BinOp::Sub(_) | BinOp::SubAssign(_))
            && self.has_dominating_guard(&expr.left, &expr.right)
        {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        let line = get_op_line(&expr.op);
        let snippet = snippet_at_line(&self.ctx.source, line);

        if !snippet.contains("checked_") && !snippet.contains("saturating_") {
            self.findings.push(Finding {
                detector_id: "INK-002".to_string(),
                name: "ink-integer-overflow".to_string(),
                severity: Severity::Low,
                confidence: Confidence::Medium,
                message: format!(
                    "Unchecked arithmetic on Balance/u128: {}",
                    expr.to_token_stream()
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: 1,
                snippet,
                recommendation: "cargo-contract enables overflow-checks by default (panics safely). Use checked_add(), checked_sub(), checked_mul() for graceful error handling. Only critical if overflow-checks manually disabled".to_string(),
                chain: Chain::Ink,
            });
        }

        syn::visit::visit_expr_binary(self, expr);
    }
}

impl<'a> OverflowVisitor<'a> {
    /// True if the enclosing function body contains a comparison guard relating
    /// the two operands (e.g. `a >= b`, `b <= a`) — the classic safe
    /// guard-then-subtract idiom. Works across `if`, `assert!`, and `ensure!`
    /// because all serialize the comparison into the body token stream.
    fn has_dominating_guard(&self, left: &Expr, right: &Expr) -> bool {
        let l = strip_ws(&left.to_token_stream().to_string());
        let r = strip_ws(&right.to_token_stream().to_string());
        if l.is_empty() || r.is_empty() {
            return false;
        }
        let candidates = [
            format!("{l}>={r}"),
            format!("{l}>{r}"),
            format!("{r}<={l}"),
            format!("{r}<{l}"),
        ];
        candidates
            .iter()
            .any(|c| self.body_normalized.contains(c.as_str()))
    }
}

/// Remove all whitespace from a string (for structural token matching).
fn strip_ws(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

/// True if the attribute list marks a test function.
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
            let tokens = a.meta.to_token_stream().to_string();
            tokens.contains("test")
        } else {
            false
        }
    })
}

/// True if a syn type's tokens mention Balance or u128.
fn type_is_balance(ty: &Type) -> bool {
    let t = ty.to_token_stream().to_string();
    t.contains("Balance") || t.contains("u128")
}

/// Collect identifiers bound to a Balance/u128 type via params or typed lets.
fn collect_balance_idents(func: &ItemFn) -> Vec<String> {
    let mut ids = Vec::new();

    for input in &func.sig.inputs {
        if let FnArg::Typed(pt) = input {
            if type_is_balance(&pt.ty) {
                if let Pat::Ident(pi) = &*pt.pat {
                    ids.push(pi.ident.to_string());
                }
            }
        }
    }

    struct LetVisitor {
        ids: Vec<String>,
    }
    impl<'ast> Visit<'ast> for LetVisitor {
        fn visit_local(&mut self, local: &'ast Local) {
            if let Pat::Type(pt) = &local.pat {
                if type_is_balance(&pt.ty) {
                    if let Pat::Ident(pi) = &*pt.pat {
                        self.ids.push(pi.ident.to_string());
                    }
                }
            }
            syn::visit::visit_local(self, local);
        }
    }
    let mut lv = LetVisitor { ids: Vec::new() };
    lv.visit_block(&func.block);
    ids.extend(lv.ids);

    ids
}

/// True if the token text contains `word` as a whole identifier token.
fn contains_word(text: &str, word: &str) -> bool {
    text.split(|c: char| !c.is_alphanumeric() && c != '_')
        .any(|t| t == word)
}

/// Heuristic: does this operand plausibly carry a Balance/u128 value?
fn operand_is_balance_like(expr: &Expr, balance_idents: &[String]) -> bool {
    let text = expr.to_token_stream().to_string();

    // Explicit type evidence (casts like `x as u128`, typed paths).
    if text.contains("Balance") || text.contains("u128") {
        return true;
    }

    // Name-based heuristic on the operand text.
    let lower = text.to_lowercase();
    const KEYWORDS: &[&str] = &[
        "balance",
        "amount",
        "supply",
        "total",
        "value",
        "deposit",
        "reward",
        "stake",
        "allowance",
        "funds",
        "payout",
        "collateral",
        "liquidity",
        "escrow",
        "dividend",
        "principal",
    ];
    for kw in KEYWORDS {
        if lower.contains(kw) {
            return true;
        }
    }

    // Resolve against operands proven to be Balance/u128 by declared type.
    for id in balance_idents {
        if contains_word(&text, id) {
            return true;
        }
    }

    false
}

/// True if the expression is a string value (literal or String construction),
/// meaning a `+` is std string concatenation rather than integer arithmetic.
fn is_string_expr(expr: &Expr) -> bool {
    if let Expr::Lit(lit) = expr {
        if let Lit::Str(_) = &lit.lit {
            return true;
        }
    }
    let text = expr.to_token_stream().to_string();
    text.contains("String :: from")
        || text.contains("String :: new")
        || text.contains(". to_string")
        || text.contains(". to_owned")
        || text.contains("format !")
}

fn get_op_line(op: &BinOp) -> usize {
    let span = match op {
        BinOp::Add(t) => t.span,
        BinOp::Sub(t) => t.span,
        BinOp::Mul(t) => t.span,
        BinOp::AddAssign(t) => t.spans[0],
        BinOp::SubAssign(t) => t.spans[0],
        BinOp::MulAssign(t) => t.spans[0],
        _ => proc_macro2::Span::call_site(),
    };
    span_to_line(&span)
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
        IntegerOverflowDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_balance_overflow() {
        let source = r#"
            // #[ink(message)]
            fn transfer(&mut self, amount: Balance) {
                self.total = self.total + amount;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect unchecked Balance arithmetic"
        );
    }

    #[test]
    fn test_no_finding_checked() {
        let source = r#"
            // #[ink(message)]
            fn transfer(&mut self, amount: Balance) -> Result<(), Error> {
                self.total = self.total.checked_add(amount).ok_or(Error::Overflow)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag checked arithmetic");
    }

    // FP1: subtraction dominated by an explicit comparison guard cannot underflow.
    #[test]
    fn test_no_finding_guarded_subtraction() {
        let source = r#"
            // #[ink(message)]
            fn debit(balance: Balance, amount: Balance) -> Balance {
                assert!(balance >= amount, "insufficient balance");
                balance - amount
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag guard-then-subtract, got: {:?}",
            findings
        );
    }

    #[test]
    fn test_still_flags_unguarded_subtraction() {
        let source = r#"
            // #[ink(message)]
            fn debit(balance: Balance, amount: Balance) -> Balance {
                balance - amount
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Unguarded Balance subtraction must still be flagged"
        );
    }

    // FP2: usize index/counter arithmetic inside a Balance-gated function.
    #[test]
    fn test_no_finding_index_arithmetic() {
        let source = r#"
            // #[ink(message)]
            fn find_holder(holders: &[AccountId], balances: &[Balance], start: usize) -> usize {
                let mut i = start;
                while i + 1 < holders.len() {
                    i = i + 1;
                }
                i
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag usize index arithmetic, got: {:?}",
            findings
        );
    }

    // FP3: "Balance"/"u128" appearing only in doc comments must not gate the fn.
    #[test]
    fn test_no_finding_doc_comment_gate() {
        let source = r#"
            // #[ink(message)]
            /// Fee helper. Result always fits: inputs are Permill (<= 1_000_000),
            /// far below u128 territory - no Balance is touched here.
            fn permill_to_bps(permill: u32) -> u32 {
                (permill / 100) * 10
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag u32 math gated only by a doc comment, got: {:?}",
            findings
        );
    }

    // FP4: String + &str concatenation is not integer arithmetic.
    #[test]
    fn test_no_finding_string_concat() {
        let source = r#"
            // #[ink(message)]
            fn balance_label(owner_name: &str, balance: Balance) -> String {
                let label = String::from("balance of ") + owner_name;
                label
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag string concatenation, got: {:?}",
            findings
        );
    }
}
