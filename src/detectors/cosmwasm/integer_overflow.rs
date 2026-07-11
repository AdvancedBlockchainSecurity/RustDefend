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
            fn_body_src: String::new(),
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
    /// Token-stream source of the current function body, for guard detection.
    fn_body_src: String,
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
        let prev_body = std::mem::take(&mut self.fn_body_src);

        self.uint_idents = collect_uint_idents(func);
        self.fn_body_src = fn_body_source(func);
        self.in_uint_fn = true;

        syn::visit::visit_item_fn(self, func);

        self.in_uint_fn = prev_in;
        self.uint_idents = prev_idents;
        self.fn_body_src = prev_body;
    }

    fn visit_expr_binary(&mut self, expr: &'ast ExprBinary) {
        if !self.in_uint_fn {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // Division is intentionally excluded: unsigned integer division cannot
        // overflow. Its only failure mode is divide-by-zero, which is a
        // different (and out-of-scope) class and panics-reverts safely anyway.
        let is_arithmetic =
            matches!(expr.op, BinOp::Add(_) | BinOp::Sub(_) | BinOp::Mul(_));

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
        if matches!(expr.op, BinOp::Sub(_))
            && sub_is_guarded(&expr.left, &expr.right, &self.fn_body_src)
        {
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
        syn::Expr::Binary(b) => {
            is_uint_operand(&b.left, uints) || is_uint_operand(&b.right, uints)
        }
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
                return s.chars().all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
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

/// True if a `left - right` subtraction is dominated by a comparison guard over
/// the same two operand identifiers (either order), which the standard
/// audited CosmWasm insufficient-funds idiom relies on.
fn sub_is_guarded(left: &syn::Expr, right: &syn::Expr, body_src: &str) -> bool {
    let (l, r) = match (expr_ident(left), expr_ident(right)) {
        (Some(l), Some(r)) => (l, r),
        _ => return false,
    };

    // body_src is a token-stream string with single-space separators, so a
    // relational expression appears verbatim as e.g. "balance < amount".
    for op in ["<", "<=", ">", ">=", "==", "!="] {
        if body_src.contains(&format!("{} {} {}", l, op, r))
            || body_src.contains(&format!("{} {} {}", r, op, l))
        {
            return true;
        }
    }
    false
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
