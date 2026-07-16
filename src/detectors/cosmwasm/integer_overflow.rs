use std::collections::HashSet;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{BinOp, ExprBinary, ItemFn};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct IntegerOverflowDetector;

impl Detector for IntegerOverflowDetector {
    fn id(&self) -> &'static str {
        "CW-001"
    }
    fn name(&self) -> &'static str {
        "cosmwasm-integer-overflow"
    }
    fn description(&self) -> &'static str {
        "Detects unchecked arithmetic on Uint128/Uint256 types (panics safely but checked_* enables graceful handling)"
    }
    fn severity(&self) -> Severity {
        Severity::Low
    }
    fn confidence(&self) -> Confidence {
        Confidence::Low
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Skip test/mock file paths
        let file_str = ctx.file_path.to_string_lossy();
        if file_str.contains("/testing")
            || file_str.contains("/mock")
            || file_str.contains("/testutils")
            || file_str.contains("_test.rs")
            || file_str.contains("integration_tests")
            || file_str.contains("multitest")
            // Cargo's canonical top-level integration-test directory: never
            // compiled into the contract wasm, so no on-chain attack surface.
            || file_str.contains("/tests/")
            || file_str.starts_with("tests/")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = OverflowVisitor {
            findings: &mut findings,
            ctx,
            in_uint_fn: false,
            uint_idents: HashSet::new(),
            proven_ge: Vec::new(),
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct OverflowVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    in_uint_fn: bool,
    /// Identifiers (fn params + `let` bindings) known to be Uint128/Uint256 in
    /// the function currently being visited.
    uint_idents: HashSet<String>,
    /// Facts `(l, r)` meaning `l >= r` is provable at the current point, each
    /// established by a guard that actually *dominates* it. Pushed on entry to
    /// a guarded region, truncated back off on exit.
    proven_ge: Vec<(String, String)>,
}

impl<'ast, 'a> Visit<'ast> for OverflowVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        // Skip `#[cfg(test)]` modules entirely — test-only code, no on-chain
        // attack surface, and a panic there merely fails a test.
        if has_cfg_test(&module.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test/mock/helper functions
        if fn_name.starts_with("test_")
            || fn_name.ends_with("_test")
            || fn_name.contains("_works")
            || fn_name.contains("_mock")
            || fn_name.starts_with("mock_")
            || fn_name.starts_with("setup")
            || fn_name.starts_with("helper")
            // Catches #[test], #[tokio::test], #[ink::test], etc. (last path
            // segment == "test"), which the exact-path check used to miss.
            || is_test_attr(&func.attrs)
        {
            return;
        }

        // Gate on Uint appearing in the *signature or body code only* — never
        // the attrs (doc comments serialize into to_token_stream as
        // `#[doc = "...Uint128..."]` and must not poison the function).
        let sig_and_body = format!(
            "{}{}",
            func.sig.to_token_stream(),
            func.block.to_token_stream()
        );
        let involves_uint = sig_and_body.contains("Uint128")
            || sig_and_body.contains("Uint256")
            || sig_and_body.contains("uint128")
            || sig_and_body.contains("uint256");

        if !involves_uint {
            // Still descend so nested Uint functions are not missed, but with
            // arithmetic detection disabled for this frame.
            let prev = self.in_uint_fn;
            self.in_uint_fn = false;
            syn::visit::visit_item_fn(self, func);
            self.in_uint_fn = prev;
            return;
        }

        let prev_in = self.in_uint_fn;
        let prev_idents = std::mem::take(&mut self.uint_idents);
        let prev_facts = std::mem::take(&mut self.proven_ge);

        self.uint_idents = collect_uint_idents(func);
        self.in_uint_fn = true;

        syn::visit::visit_item_fn(self, func);

        self.in_uint_fn = prev_in;
        self.uint_idents = prev_idents;
        self.proven_ge = prev_facts;
    }

    fn visit_block(&mut self, block: &'ast syn::Block) {
        // Walk statements in source order so a guard only ever establishes facts
        // for the statements that actually follow it, never the ones before it.
        let saved = self.proven_ge.len();
        for stmt in &block.stmts {
            syn::visit::visit_stmt(self, stmt);
            self.record_guard_facts(stmt);
        }
        self.proven_ge.truncate(saved);
    }

    fn visit_expr_if(&mut self, expr: &'ast syn::ExprIf) {
        // The condition itself is ordinary code — check it under current facts.
        self.visit_expr(&expr.cond);

        // Inside the `then` branch the condition holds; inside `else` it does not.
        let saved = self.proven_ge.len();
        facts_from_cond(&expr.cond, &mut self.proven_ge);
        self.visit_block(&expr.then_branch);
        self.proven_ge.truncate(saved);

        if let Some((_, else_branch)) = &expr.else_branch {
            let saved = self.proven_ge.len();
            negated_facts_from_cond(&expr.cond, &mut self.proven_ge);
            self.visit_expr(else_branch);
            self.proven_ge.truncate(saved);
        }
    }

    fn visit_expr_binary(&mut self, expr: &'ast ExprBinary) {
        if !self.in_uint_fn {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // Division is intentionally excluded: unsigned integer division cannot
        // overflow. Its only failure mode is divide-by-zero, which is a
        // different (and out-of-scope) class and panics-reverts safely anyway.
        let is_arithmetic = matches!(expr.op, BinOp::Add(_) | BinOp::Sub(_) | BinOp::Mul(_));

        if !is_arithmetic {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // Skip constant-only expressions (literals and Uint128::new(100)-style
        // constant constructors / SCREAMING_SNAKE consts): cannot overflow for
        // any input because there are no inputs.
        if is_const_operand(&expr.left) && is_const_operand(&expr.right) {
            return;
        }

        // Only flag when an operand of *this specific* expression actually
        // resolves to a Uint128/Uint256 value. A Uint param elsewhere in the
        // signature must not make unrelated u64/usize math a finding.
        if !(is_uint_operand(&expr.left, &self.uint_idents)
            || is_uint_operand(&expr.right, &self.uint_idents))
        {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // A dominating comparison guard over the same operands (the pervasive
        // `if balance < amount { return Err(..) }` / `ensure!(balance >= amount)`
        // idiom) makes the subtraction provably unable to underflow.
        if matches!(expr.op, BinOp::Sub(_)) && self.sub_is_guarded(&expr.left, &expr.right) {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        let line = get_expr_line(expr);
        let snippet = snippet_at_line(&self.ctx.source, line);

        if !(snippet.contains("checked_") || snippet.contains("saturating_")) {
            let expr_str = expr.to_token_stream().to_string();
            self.findings.push(Finding {
                detector_id: "CW-001".to_string(),
                name: "cosmwasm-integer-overflow".to_string(),
                severity: Severity::Low,
                confidence: Confidence::Low,
                message: format!(
                    "Unchecked arithmetic on Uint128/Uint256: {}",
                    expr_str
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: 1,
                snippet,
                recommendation: "Uint128/Uint256 operators panic on overflow (safe revert). Use checked_add(), checked_sub(), checked_mul() for graceful error handling instead of panics".to_string(),
                chain: Chain::CosmWasm,
            });
        }

        syn::visit::visit_expr_binary(self, expr);
    }
}

impl<'a> OverflowVisitor<'a> {
    /// Record the facts a *statement-position* guard establishes for everything
    /// that follows it in the same block: either `if <cmp> { return Err(..) }`
    /// (reachable code below implies the condition was false) or an
    /// `ensure!/require!/assert!(<cmp>, ..)` (reachable code below implies it
    /// held). Anything else — a `let`, a log line, an event attribute — merely
    /// *computes* a comparison and guards nothing.
    fn record_guard_facts(&mut self, stmt: &syn::Stmt) {
        match stmt {
            syn::Stmt::Expr(syn::Expr::If(ei), _) => {
                // Only a `then` branch that unconditionally leaves makes the
                // negated condition hold for the code after the `if`.
                if block_diverges(&ei.then_branch) {
                    negated_facts_from_cond(&ei.cond, &mut self.proven_ge);
                }
            }
            syn::Stmt::Expr(syn::Expr::Macro(em), _) => {
                macro_guard_facts(&em.mac, &mut self.proven_ge)
            }
            syn::Stmt::Macro(sm) => macro_guard_facts(&sm.mac, &mut self.proven_ge),
            _ => {}
        }
    }

    /// True if some guard dominating this point proves `left >= right`, so the
    /// subtraction cannot underflow. Facts come only from real control flow —
    /// a comparison that is merely *computed* (`let is_full = a == b;`, an
    /// event attribute, a log line) never lands here.
    fn sub_is_guarded(&self, left: &syn::Expr, right: &syn::Expr) -> bool {
        let (l, r) = match (expr_ident(left), expr_ident(right)) {
            (Some(l), Some(r)) => (l, r),
            _ => return false,
        };
        self.proven_ge.iter().any(|(gl, gr)| *gl == l && *gr == r)
    }
}

/// True if any attribute's last path segment is `test` (`#[test]`,
/// `#[tokio::test]`, `#[ink::test]`, `#[async_std::test]`, ...).
fn is_test_attr(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

/// True if attributes contain `#[cfg(test)]` (or a `cfg(... test ...)`).
fn has_cfg_test(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path().is_ident("cfg") && attr.to_token_stream().to_string().contains("test")
    })
}

/// A syn type whose token text mentions a Uint128/Uint256 type.
fn type_is_uint(ty: &syn::Type) -> bool {
    let s = ty.to_token_stream().to_string();
    s.contains("Uint128") || s.contains("Uint256")
}

/// Collect the set of identifiers (fn params + `let` bindings) that are known
/// to hold a Uint128/Uint256 value within `func`.
fn collect_uint_idents(func: &ItemFn) -> HashSet<String> {
    let mut set = HashSet::new();

    // Parameters with an explicit Uint type.
    for input in &func.sig.inputs {
        if let syn::FnArg::Typed(pt) = input {
            if type_is_uint(&pt.ty) {
                if let syn::Pat::Ident(pi) = &*pt.pat {
                    set.insert(pi.ident.to_string());
                }
            }
        }
    }

    // `let` bindings, resolved in source order so forward references work.
    let mut collector = LocalUintCollector { set: &mut set };
    collector.visit_block(&func.block);

    set
}

struct LocalUintCollector<'a> {
    set: &'a mut HashSet<String>,
}

impl<'ast, 'a> Visit<'ast> for LocalUintCollector<'a> {
    fn visit_local(&mut self, local: &'ast syn::Local) {
        let mut ident: Option<String> = None;
        let mut is_uint = false;

        match &local.pat {
            // `let x: Uint128 = ...`
            syn::Pat::Type(pt) => {
                if let syn::Pat::Ident(pi) = &*pt.pat {
                    ident = Some(pi.ident.to_string());
                }
                if type_is_uint(&pt.ty) {
                    is_uint = true;
                }
            }
            // `let x = ...`
            syn::Pat::Ident(pi) => {
                ident = Some(pi.ident.to_string());
            }
            _ => {}
        }

        if !is_uint {
            if let Some(init) = &local.init {
                if is_uint_operand(&init.expr, self.set) {
                    is_uint = true;
                }
            }
        }

        if is_uint {
            if let Some(id) = ident {
                self.set.insert(id);
            }
        }

        syn::visit::visit_local(self, local);
    }
}

/// Does this expression resolve to a Uint128/Uint256 value?
fn is_uint_operand(expr: &syn::Expr, uints: &HashSet<String>) -> bool {
    match expr {
        syn::Expr::Path(p) => {
            if let Some(id) = p.path.get_ident() {
                if uints.contains(&id.to_string()) {
                    return true;
                }
            }
            let s = p.to_token_stream().to_string();
            s.contains("Uint128") || s.contains("Uint256")
        }
        syn::Expr::Paren(e) => is_uint_operand(&e.expr, uints),
        syn::Expr::Group(e) => is_uint_operand(&e.expr, uints),
        syn::Expr::Reference(e) => is_uint_operand(&e.expr, uints),
        syn::Expr::Try(e) => is_uint_operand(&e.expr, uints),
        // (a + b) * c — a Uint sub-expression makes the whole thing Uint.
        syn::Expr::Binary(b) => is_uint_operand(&b.left, uints) || is_uint_operand(&b.right, uints),
        // amount.multiply_ratio(..) / balance.min(..): receiver type propagates.
        syn::Expr::MethodCall(m) => is_uint_operand(&m.receiver, uints),
        // Uint128::new(..) / Uint128::from(..): inspect only the callee.
        syn::Expr::Call(c) => {
            let s = c.func.to_token_stream().to_string();
            s.contains("Uint128") || s.contains("Uint256")
        }
        syn::Expr::Cast(c) => type_is_uint(&c.ty),
        // Fields, indexes, etc. are unknown-typed unless they literally name a
        // Uint constructor path — do not assume Uint.
        _ => false,
    }
}

/// Is this expression a compile-time constant (literal, constant Uint
/// constructor, SCREAMING_SNAKE const, or arithmetic over such)?
fn is_const_operand(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Lit(_) => true,
        syn::Expr::Paren(e) => is_const_operand(&e.expr),
        syn::Expr::Group(e) => is_const_operand(&e.expr),
        syn::Expr::Unary(u) => is_const_operand(&u.expr),
        syn::Expr::Cast(c) => is_const_operand(&c.expr),
        syn::Expr::Binary(b) => is_const_operand(&b.left) && is_const_operand(&b.right),
        syn::Expr::Path(p) => {
            if let Some(id) = p.path.get_ident() {
                let s = id.to_string();
                // A const by convention: all-uppercase (with digits/underscores)
                // and containing at least one letter.
                return s
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
                    && s.chars().any(|c| c.is_ascii_uppercase());
            }
            false
        }
        // Uint128::new(100) / Uint128::from(5) / Uint256::zero() with const args.
        syn::Expr::Call(c) => {
            let func_s = c.func.to_token_stream().to_string();
            let is_uint_ctor = (func_s.contains("Uint128") || func_s.contains("Uint256"))
                && (func_s.ends_with("new")
                    || func_s.ends_with("from")
                    || func_s.ends_with("one")
                    || func_s.ends_with("zero"));
            is_uint_ctor && c.args.iter().all(is_const_operand)
        }
        _ => false,
    }
}

/// Push the `l >= r` facts that hold when `cond` is **true**.
///
/// Only relations that actually prove an ordering count. `a != b` proves
/// nothing about which side is larger and so yields no facts.
fn facts_from_cond(cond: &syn::Expr, out: &mut Vec<(String, String)>) {
    match cond {
        syn::Expr::Paren(e) => facts_from_cond(&e.expr, out),
        syn::Expr::Group(e) => facts_from_cond(&e.expr, out),
        // `!c` is true exactly when `c` is false.
        syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => {
            negated_facts_from_cond(&u.expr, out)
        }
        syn::Expr::Binary(b) => {
            // Both conjuncts of `a && b` hold.
            if matches!(b.op, BinOp::And(_)) {
                facts_from_cond(&b.left, out);
                facts_from_cond(&b.right, out);
                return;
            }
            let (l, r) = match (expr_ident(&b.left), expr_ident(&b.right)) {
                (Some(l), Some(r)) => (l, r),
                _ => return,
            };
            match b.op {
                // l >= r and l > r both prove `l - r` cannot underflow.
                BinOp::Ge(_) | BinOp::Gt(_) => out.push((l, r)),
                BinOp::Le(_) | BinOp::Lt(_) => out.push((r, l)),
                // Equality proves the ordering in both directions.
                BinOp::Eq(_) => {
                    out.push((l.clone(), r.clone()));
                    out.push((r, l));
                }
                _ => {}
            }
        }
        _ => {}
    }
}

/// Push the `l >= r` facts that hold when `cond` is **false** — i.e. the facts
/// available to code that is only reachable because the guard did not fire.
fn negated_facts_from_cond(cond: &syn::Expr, out: &mut Vec<(String, String)>) {
    match cond {
        syn::Expr::Paren(e) => negated_facts_from_cond(&e.expr, out),
        syn::Expr::Group(e) => negated_facts_from_cond(&e.expr, out),
        syn::Expr::Unary(u) if matches!(u.op, syn::UnOp::Not(_)) => facts_from_cond(&u.expr, out),
        syn::Expr::Binary(b) => {
            // `a || b` is false only when both disjuncts are false.
            if matches!(b.op, BinOp::Or(_)) {
                negated_facts_from_cond(&b.left, out);
                negated_facts_from_cond(&b.right, out);
                return;
            }
            let (l, r) = match (expr_ident(&b.left), expr_ident(&b.right)) {
                (Some(l), Some(r)) => (l, r),
                _ => return,
            };
            match b.op {
                // !(l < r) => l >= r; !(l <= r) => l > r.
                BinOp::Lt(_) | BinOp::Le(_) => out.push((l, r)),
                BinOp::Gt(_) | BinOp::Ge(_) => out.push((r, l)),
                // !(l != r) => l == r.
                BinOp::Ne(_) => {
                    out.push((l.clone(), r.clone()));
                    out.push((r, l));
                }
                _ => {}
            }
        }
        _ => {}
    }
}

/// Does this block unconditionally leave the enclosing function or loop? Only
/// then does an `if` act as a guard over the code that follows it.
fn block_diverges(block: &syn::Block) -> bool {
    block.stmts.iter().any(|stmt| match stmt {
        syn::Stmt::Expr(e, _) => expr_diverges(e),
        syn::Stmt::Macro(m) => macro_diverges(&m.mac),
        _ => false,
    })
}

fn expr_diverges(expr: &syn::Expr) -> bool {
    match expr {
        syn::Expr::Return(_) | syn::Expr::Break(_) | syn::Expr::Continue(_) => true,
        syn::Expr::Macro(m) => macro_diverges(&m.mac),
        syn::Expr::Paren(e) => expr_diverges(&e.expr),
        syn::Expr::Group(e) => expr_diverges(&e.expr),
        _ => false,
    }
}

/// `panic!`/`bail!`-style macros that never return.
fn macro_diverges(mac: &syn::Macro) -> bool {
    mac.path
        .segments
        .last()
        .map(|s| {
            matches!(
                s.ident.to_string().as_str(),
                "panic" | "unreachable" | "todo" | "unimplemented" | "bail"
            )
        })
        .unwrap_or(false)
}

/// Facts established by an `ensure!(cond, ..)` / `require!(cond, ..)` /
/// `assert!(cond)` statement: reachable code below it implies `cond` held.
fn macro_guard_facts(mac: &syn::Macro, out: &mut Vec<(String, String)>) {
    let asserts_cond = mac
        .path
        .segments
        .last()
        .map(|s| {
            matches!(
                s.ident.to_string().as_str(),
                "ensure" | "require" | "assert" | "debug_assert"
            )
        })
        .unwrap_or(false);
    if !asserts_cond {
        return;
    }

    // The condition is the first comma-separated argument; the rest is the
    // error value / format args and is irrelevant here.
    let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
    if let Ok(args) = mac.parse_body_with(parser) {
        if let Some(cond) = args.first() {
            facts_from_cond(cond, out);
        }
    }
}

/// The single identifier of a simple path expression, if any.
fn expr_ident(expr: &syn::Expr) -> Option<String> {
    if let syn::Expr::Path(p) = expr {
        if let Some(id) = p.path.get_ident() {
            return Some(id.to_string());
        }
    }
    None
}

fn get_expr_line(expr: &ExprBinary) -> usize {
    let span = match &expr.op {
        BinOp::Add(t) => t.span,
        BinOp::Sub(t) => t.span,
        BinOp::Mul(t) => t.span,
        BinOp::Div(t) => t.span,
        _ => proc_macro2::Span::call_site(),
    };
    span_to_line(&span)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_detector(source: &str) -> Vec<Finding> {
        run_detector_with_path(source, "test.rs")
    }

    fn run_detector_with_path(source: &str, path: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let ctx = ScanContext::new(
            std::path::PathBuf::from(path),
            source.to_string(),
            ast,
            Chain::CosmWasm,
            std::collections::HashMap::new(),
        );
        IntegerOverflowDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_uint128_overflow() {
        let source = r#"
            fn add_amounts(a: Uint128, b: Uint128) -> Uint128 {
                a + b
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect unchecked Uint128 arithmetic"
        );
    }

    #[test]
    fn test_no_finding_checked() {
        let source = r#"
            fn add_amounts(a: Uint128, b: Uint128) -> StdResult<Uint128> {
                a.checked_add(b)
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag checked arithmetic");
    }

    // --- FP #0: non-Uint arithmetic in a fn that merely has a Uint param ---
    #[test]
    fn test_no_finding_non_uint_arithmetic_in_uint_fn() {
        let source = r#"
            pub fn execute_claim(amount: Uint128, lock_duration: u64) -> u64 {
                let base = 100u64;
                let unlock_at = base + lock_duration;
                let mut acc = 0usize;
                for i in 0..10 {
                    acc = i + 1;
                }
                unlock_at
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "u64/usize arithmetic must not be flagged just because a Uint128 param exists: {:?}",
            findings
        );
    }

    // --- FP #1: guarded subtraction (insufficient-funds idiom) ---
    #[test]
    fn test_no_finding_guarded_subtraction() {
        let source = r#"
            fn withdraw(balance: Uint128, amount: Uint128) -> Result<Uint128, ContractError> {
                if balance < amount {
                    return Err(ContractError::InsufficientFunds {});
                }
                Ok(balance - amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Comparison-guarded subtraction must not be flagged: {:?}",
            findings
        );
    }

    #[test]
    fn test_no_finding_ensure_guarded_subtraction() {
        let source = r#"
            fn withdraw(balance: Uint128, amount: Uint128) -> Result<Uint128, ContractError> {
                ensure!(balance >= amount, ContractError::InsufficientFunds {});
                Ok(balance - amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "ensure!-guarded subtraction must not be flagged: {:?}",
            findings
        );
    }

    // The positive form of the idiom: the subtraction sits in the branch where
    // the comparison is known to hold.
    #[test]
    fn test_no_finding_subtraction_in_guarded_branch() {
        let source = r#"
            fn withdraw(balance: Uint128, amount: Uint128) -> Result<Uint128, ContractError> {
                if balance >= amount {
                    Ok(balance - amount)
                } else {
                    Err(ContractError::InsufficientFunds {})
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Subtraction inside the branch where the guard holds must not be flagged: {:?}",
            findings
        );
    }

    // --- REGRESSION (ADV-206 false negative) ---
    // The guard used to be a substring scan of the whole function body, so any
    // textual occurrence of the two operands around a relational operator
    // silenced the subtraction. Here `balance == amount` only computes an event
    // attribute — it gates nothing, execution continues either way, and
    // `balance - amount` underflows for `amount > balance`. MUST fire.
    #[test]
    fn test_still_flags_subtraction_with_non_guarding_comparison() {
        let source = r#"
            pub fn execute_withdraw(deps: DepsMut, info: MessageInfo, amount: Uint128) -> Result<Response, ContractError> {
                let balance: Uint128 = BALANCES
                    .load(deps.storage, info.sender.as_str())
                    .unwrap_or_default();

                // Indexer hint only. Not a guard: no early return, no ensure!.
                let is_full_withdrawal = balance == amount;

                let remaining = balance - amount;

                BALANCES.save(deps.storage, info.sender.as_str(), &remaining).ok();

                Ok(Response::new()
                    .add_attribute("action", "withdraw")
                    .add_attribute("full_withdrawal", is_full_withdrawal.to_string()))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A comparison that only computes a value must not suppress the underflow: {:?}",
            findings
        );
    }

    // A comparison inside an `if` whose body does NOT leave the function guards
    // nothing — execution falls through to the subtraction regardless.
    #[test]
    fn test_still_flags_subtraction_after_non_diverging_if() {
        let source = r#"
            fn withdraw(balance: Uint128, amount: Uint128) -> Uint128 {
                if balance < amount {
                    deps.api.debug("overdrawn");
                }
                balance - amount
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "An if-guard that does not return/panic must not suppress the underflow: {:?}",
            findings
        );
    }

    // The guard must be direction-aware: this one is inverted, so it rejects
    // exactly the safe calls and lets the underflowing ones through.
    #[test]
    fn test_still_flags_inverted_guard() {
        let source = r#"
            fn withdraw(balance: Uint128, amount: Uint128) -> Result<Uint128, ContractError> {
                if balance > amount {
                    return Err(ContractError::InsufficientFunds {});
                }
                Ok(balance - amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "An inverted guard proves nothing and must not suppress: {:?}",
            findings
        );
    }

    // Guard must dominate: comparing *after* the subtraction is too late.
    #[test]
    fn test_still_flags_subtraction_before_guard() {
        let source = r#"
            fn withdraw(balance: Uint128, amount: Uint128) -> Result<Uint128, ContractError> {
                let remaining = balance - amount;
                if balance < amount {
                    return Err(ContractError::InsufficientFunds {});
                }
                Ok(remaining)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A guard placed after the subtraction cannot make it safe: {:?}",
            findings
        );
    }

    // Guard must NOT over-suppress: an unguarded subtraction still fires.
    #[test]
    fn test_still_flags_unguarded_subtraction() {
        let source = r#"
            fn withdraw(balance: Uint128, amount: Uint128) -> Uint128 {
                balance - amount
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Unguarded Uint128 subtraction should still be flagged"
        );
    }

    // --- FP #2: division cannot overflow on unsigned types ---
    #[test]
    fn test_no_finding_division() {
        let source = r#"
            fn average_stake(total: Uint128, num_stakers: Uint128) -> Uint128 {
                total / num_stakers
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Unsigned division cannot overflow and must not be flagged: {:?}",
            findings
        );
    }

    // --- FP #3: "Uint128" appearing only in a doc comment ---
    #[test]
    fn test_no_finding_uint_only_in_doc_comment() {
        let source = r#"
            /// Migrates legacy u64 balances (stored before we switched to Uint128).
            fn bump_version(stored: u64, delta: u64) -> u64 {
                stored + delta
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "u64 math must not be flagged when Uint128 is only in a doc comment: {:?}",
            findings
        );
    }

    // --- FP #4: helper in a Cargo tests/ directory file ---
    #[test]
    fn test_no_finding_in_tests_directory() {
        let source = r#"
            fn seed_balances(base: Uint128, bonus: Uint128) -> Uint128 {
                base + bonus
            }
        "#;
        let findings = run_detector_with_path(source, "tests/staking.rs");
        assert!(
            findings.is_empty(),
            "Helpers under tests/ are not compiled into wasm and must be skipped: {:?}",
            findings
        );
    }

    // --- FP #5: constant-only Uint128 arithmetic via constructors ---
    #[test]
    fn test_no_finding_constant_constructor_arithmetic() {
        let source = r#"
            fn default_fee() -> Uint128 {
                Uint128::new(100) * Uint128::new(25)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Compile-time-constant Uint128 arithmetic must not be flagged: {:?}",
            findings
        );
    }

    // --- cfg(test) module should be skipped ---
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                fn compute(a: Uint128, b: Uint128) -> Uint128 {
                    a + b
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Arithmetic inside #[cfg(test)] modules must be skipped: {:?}",
            findings
        );
    }
}
