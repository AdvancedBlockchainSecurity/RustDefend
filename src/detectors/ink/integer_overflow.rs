use quote::ToTokens;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{
    Attribute, BinOp, Block, Expr, ExprBinary, ExprIf, FnArg, ItemFn, ItemMod, Lit, Local, Macro,
    Pat, Stmt, Token, Type, UnOp,
};

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
            active_guards: Vec::new(),
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// A comparison fact `left >= right` proven to hold at the current program
/// point by a guard that dominates it. Operands are whitespace-stripped token
/// text so they can be matched against an arithmetic expression's operands.
struct GuardFact {
    left: String,
    right: String,
}

struct OverflowVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    in_function: bool,
    /// Identifiers (params / typed let-bindings) whose declared type is Balance/u128.
    balance_idents: Vec<String>,
    /// Comparison facts established by guards that dominate the current program
    /// point. Pushed on entry to a guarded scope (or by an already-executed
    /// `assert!`/early-return in the enclosing block) and popped on scope exit.
    active_guards: Vec<GuardFact>,
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
            let prev_guards = std::mem::take(&mut self.active_guards);

            self.in_function = true;
            self.balance_idents = balance_idents;

            syn::visit::visit_item_fn(self, func);

            self.in_function = prev_in;
            self.balance_idents = prev_ids;
            self.active_guards = prev_guards;
        } else {
            // Recurse (e.g. for nested items) but do not flag arithmetic here.
            let prev_in = self.in_function;
            self.in_function = false;
            syn::visit::visit_item_fn(self, func);
            self.in_function = prev_in;
        }
    }

    fn visit_block(&mut self, block: &'ast Block) {
        // Walk statements in execution order. A guard only dominates the
        // statements that FOLLOW it, so facts are collected after each
        // statement is visited, and dropped when the block's scope ends.
        let depth = self.active_guards.len();
        for stmt in &block.stmts {
            syn::visit::visit_stmt(self, stmt);
            self.push_stmt_facts(stmt);
        }
        self.active_guards.truncate(depth);
    }

    fn visit_expr_if(&mut self, i: &'ast ExprIf) {
        // The condition itself is evaluated unguarded.
        self.visit_expr(&i.cond);

        // `if a >= b { .. }` proves `a >= b` inside the then-branch only.
        let depth = self.active_guards.len();
        self.push_facts(&i.cond, true);
        self.visit_block(&i.then_branch);
        self.active_guards.truncate(depth);

        // ...and its negation inside the else-branch.
        if let Some((_, else_branch)) = &i.else_branch {
            let depth = self.active_guards.len();
            self.push_facts(&i.cond, false);
            self.visit_expr(else_branch);
            self.active_guards.truncate(depth);
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
    /// True if `left >= right` is proven by a guard that actually dominates this
    /// program point — the classic safe guard-then-subtract idiom.
    ///
    /// Only facts pushed by an ENFORCING construct count: an `assert!`/`ensure!`
    /// condition, an `if cond { .. }` whose branch encloses this expression, or
    /// an `if !cond { return .. }` early-return earlier in the same block. A
    /// comparison that merely appears in the body (e.g. bound to a `let` and
    /// never acted on) proves nothing and is deliberately not consulted.
    fn has_dominating_guard(&self, left: &Expr, right: &Expr) -> bool {
        let l = strip_ws(&left.to_token_stream().to_string());
        let r = strip_ws(&right.to_token_stream().to_string());
        if l.is_empty() || r.is_empty() {
            return false;
        }
        self.active_guards
            .iter()
            .any(|g| g.left == l && g.right == r)
    }

    /// Record the comparison facts implied by `cond` holding (`positive`) or by
    /// `cond` failing (`!positive`), normalised to the form `left >= right`.
    fn push_facts(&mut self, cond: &Expr, positive: bool) {
        match cond {
            Expr::Paren(p) => self.push_facts(&p.expr, positive),
            Expr::Group(g) => self.push_facts(&g.expr, positive),
            Expr::Unary(u) if matches!(u.op, UnOp::Not(_)) => self.push_facts(&u.expr, !positive),
            Expr::Binary(b) => {
                let l = strip_ws(&b.left.to_token_stream().to_string());
                let r = strip_ws(&b.right.to_token_stream().to_string());
                match (&b.op, positive) {
                    // `a && b` proves both conjuncts; by De Morgan, a failing
                    // `a || b` disproves both disjuncts.
                    (BinOp::And(_), true) | (BinOp::Or(_), false) => {
                        self.push_facts(&b.left, positive);
                        self.push_facts(&b.right, positive);
                    }
                    // `a >= b`, `a > b`, `!(a < b)` and `!(a <= b)` all prove `a >= b`.
                    (BinOp::Ge(_), true)
                    | (BinOp::Gt(_), true)
                    | (BinOp::Lt(_), false)
                    | (BinOp::Le(_), false) => {
                        self.active_guards.push(GuardFact { left: l, right: r });
                    }
                    // `a <= b`, `a < b`, `!(a > b)` and `!(a >= b)` all prove `b >= a`.
                    (BinOp::Le(_), true)
                    | (BinOp::Lt(_), true)
                    | (BinOp::Gt(_), false)
                    | (BinOp::Ge(_), false) => {
                        self.active_guards.push(GuardFact { left: r, right: l });
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    /// Facts that hold for the remainder of a block once `stmt` has executed.
    fn push_stmt_facts(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Macro(m) => self.push_macro_facts(&m.mac),
            Stmt::Expr(expr, _) => self.push_expr_stmt_facts(expr),
            _ => {}
        }
    }

    fn push_expr_stmt_facts(&mut self, expr: &Expr) {
        match expr {
            // `assert!(a >= b, "..")` / `ensure!(a >= b, Error::X)`.
            Expr::Macro(m) => self.push_macro_facts(&m.mac),
            // `ensure!(a >= b, Error::X)?;`
            Expr::Try(t) => self.push_expr_stmt_facts(&t.expr),
            // Early-return guard: `if a < b { return Err(..); }` proves `a >= b`
            // for everything after it. Requires no `else`, and a then-branch
            // that cannot fall through.
            Expr::If(i) if i.else_branch.is_none() && block_diverges(&i.then_branch) => {
                self.push_facts(&i.cond, false);
            }
            _ => {}
        }
    }

    /// Facts proven by an assertion-style macro whose condition is enforced at
    /// run time (it panics or returns early when the condition fails).
    fn push_macro_facts(&mut self, mac: &Macro) {
        let name = mac
            .path
            .segments
            .last()
            .map(|s| s.ident.to_string())
            .unwrap_or_default();
        if !matches!(
            name.as_str(),
            "assert" | "debug_assert" | "ensure" | "require"
        ) {
            return;
        }
        if let Some(cond) = macro_first_arg(mac) {
            self.push_facts(&cond, true);
        }
    }
}

/// Parse a macro's first comma-separated argument as an expression, i.e. the
/// condition of `assert!(cond, "msg")` / `ensure!(cond, Error::X)`.
fn macro_first_arg(mac: &Macro) -> Option<Expr> {
    mac.parse_body_with(Punctuated::<Expr, Token![,]>::parse_terminated)
        .ok()
        .and_then(|args| args.into_iter().next())
}

/// True if the block cannot fall through to the code following its enclosing
/// `if` — it returns, breaks, continues, or panics.
fn block_diverges(block: &Block) -> bool {
    match block.stmts.last() {
        Some(Stmt::Expr(expr, _)) => expr_diverges(expr),
        Some(Stmt::Macro(m)) => is_diverging_macro(&m.mac),
        _ => false,
    }
}

fn expr_diverges(expr: &Expr) -> bool {
    match expr {
        Expr::Return(_) | Expr::Break(_) | Expr::Continue(_) => true,
        Expr::Macro(m) => is_diverging_macro(&m.mac),
        _ => false,
    }
}

fn is_diverging_macro(mac: &Macro) -> bool {
    mac.path
        .segments
        .last()
        .map(|s| {
            matches!(
                s.ident.to_string().as_str(),
                "panic" | "unreachable" | "todo" | "unimplemented"
            )
        })
        .unwrap_or(false)
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

    // REGRESSION (INK-002 false negative): a comparison bound to a `let` and
    // never enforced is advisory only — the subtraction still executes on every
    // path and still underflows. Naming the comparison must not silence us.
    #[test]
    fn test_still_flags_advisory_comparison_subtraction() {
        let source = r#"
            // #[ink(message)]
            fn apply_withdrawal(balance: Balance, amount: Balance) -> (Balance, bool) {
                // Audit flag for the Withdrawn event. Advisory only.
                let sufficient = balance >= amount;
                let remaining = balance - amount;
                (remaining, sufficient)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Unenforced `let sufficient = balance >= amount` must not suppress the \
             underflowing subtraction"
        );
    }

    // The guard must dominate: a check performed AFTER the subtraction is too late.
    #[test]
    fn test_still_flags_subtraction_before_guard() {
        let source = r#"
            // #[ink(message)]
            fn debit(balance: Balance, amount: Balance) -> Balance {
                let remaining = balance - amount;
                assert!(balance >= amount, "insufficient balance");
                remaining
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A guard after the subtraction does not dominate it and must not suppress"
        );
    }

    // A guard confined to an unrelated branch does not dominate the subtraction.
    #[test]
    fn test_still_flags_guard_in_other_branch() {
        let source = r#"
            // #[ink(message)]
            fn debit(balance: Balance, amount: Balance, fee_only: bool) -> Balance {
                if balance >= amount {
                    return balance;
                }
                balance - amount
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Subtraction on the path where `balance >= amount` is FALSE must be flagged"
        );
    }

    // FP1 (structural): early-return guard dominating the subtraction.
    #[test]
    fn test_no_finding_early_return_guard() {
        let source = r#"
            // #[ink(message)]
            fn debit(balance: Balance, amount: Balance) -> Result<Balance, Error> {
                if balance < amount {
                    return Err(Error::InsufficientFunds);
                }
                Ok(balance - amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag subtraction behind an early-return guard, got: {:?}",
            findings
        );
    }

    // FP1 (structural): subtraction enclosed by the guarded branch.
    #[test]
    fn test_no_finding_if_branch_guard() {
        let source = r#"
            // #[ink(message)]
            fn debit(balance: Balance, amount: Balance) -> Balance {
                if balance >= amount {
                    balance - amount
                } else {
                    0
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag subtraction inside an `if a >= b` branch, got: {:?}",
            findings
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
