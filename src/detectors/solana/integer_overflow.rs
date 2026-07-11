use quote::ToTokens;
use syn::visit::Visit;
use syn::{BinOp, Expr, ExprBinary, ExprMethodCall, ImplItemFn, ItemFn};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct IntegerOverflowDetector;

impl Detector for IntegerOverflowDetector {
    fn id(&self) -> &'static str {
        "SOL-003"
    }
    fn name(&self) -> &'static str {
        "integer-overflow"
    }
    fn description(&self) -> &'static str {
        "Detects unchecked arithmetic operations on integer types"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Only fire on Solana code — require Solana-specific markers in source
        if !ctx.source.contains("solana_program")
            && !ctx.source.contains("anchor_lang")
            && !ctx.source.contains("Pubkey")
            && !ctx.source.contains("AccountInfo")
            && !ctx.source.contains("ProgramResult")
            && !ctx.source.contains("solana_sdk")
        {
            return Vec::new();
        }

        // Skip framework/library source — SPL and Anchor intentionally use
        // raw arithmetic with documented overflow properties
        let file_str = ctx.file_path.to_string_lossy();
        if file_str.contains("/spl-token")
            || file_str.contains("/spl_token")
            || file_str.contains("/anchor-lang/")
            || file_str.contains("/anchor_lang/")
            || file_str.contains("/anchor/lang/")
            || file_str.contains("/solana-program/")
            || file_str.contains("/solana_program/")
            || file_str.contains("/token-swap/")
            || file_str.contains("/token_swap/")
            || file_str.contains("/stake-pool/")
            || file_str.contains("/lending/")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = OverflowVisitor {
            findings: &mut findings,
            ctx,
            in_function: false,
            current_fn_name: String::new(),
            current_fn_float_params: Vec::new(),
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct OverflowVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    in_function: bool,
    current_fn_name: String,
    /// Names of parameters of the current function whose declared type is a
    /// floating-point type (f32/f64). Arithmetic on these operands cannot cause
    /// integer overflow (IEEE-754 saturates to +/-inf), so it is skipped.
    current_fn_float_params: Vec<String>,
}

impl<'ast, 'a> Visit<'ast> for OverflowVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        // Skip `#[cfg(test)]` modules entirely — code compiled only under the
        // test profile never ships on-chain, and cargo's test profile enables
        // overflow checks anyway, so there is no attacker-reachable overflow.
        if has_attribute_with_value(&module.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip serialization/pack functions (bounded offset arithmetic)
        if is_pack_fn(&fn_name) {
            return;
        }

        // Skip test functions
        if is_test_fn(&fn_name, &func.attrs) {
            return;
        }

        // Skip fee/swap calculator functions — arithmetic is intentional and
        // typically bounded by prior validation or uses checked math internally
        if is_math_helper_fn(&fn_name) {
            return;
        }

        let body_src = fn_body_source(func);
        // Skip if function exclusively uses checked arithmetic
        if !body_src.contains('+')
            && !body_src.contains('-')
            && !body_src.contains('*')
            && !body_src.contains('/')
        {
            return;
        }

        // Skip functions that validate inputs before arithmetic
        if fn_has_bounds_check(&body_src, &func.block, &self.ctx.ast) {
            return;
        }

        self.in_function = true;
        self.current_fn_name = fn_name;
        self.current_fn_float_params = float_params_of_sig(&func.sig);
        syn::visit::visit_item_fn(self, func);
        self.in_function = false;
        self.current_fn_name.clear();
        self.current_fn_float_params.clear();
    }

    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        let fn_name = method.sig.ident.to_string();

        // Skip serialization/pack functions
        if is_pack_fn(&fn_name) {
            return;
        }

        // Skip test functions
        if is_test_fn(&fn_name, &method.attrs) {
            return;
        }

        // Skip fee/swap calculator functions
        if is_math_helper_fn(&fn_name) {
            return;
        }

        let body_src = method.block.to_token_stream().to_string();
        if !body_src.contains('+')
            && !body_src.contains('-')
            && !body_src.contains('*')
            && !body_src.contains('/')
        {
            return;
        }

        // Skip functions that validate inputs before arithmetic
        if fn_has_bounds_check(&body_src, &method.block, &self.ctx.ast) {
            return;
        }

        self.in_function = true;
        self.current_fn_name = fn_name;
        self.current_fn_float_params = float_params_of_sig(&method.sig);
        syn::visit::visit_impl_item_fn(self, method);
        self.in_function = false;
        self.current_fn_name.clear();
        self.current_fn_float_params.clear();
    }

    fn visit_expr_binary(&mut self, expr: &'ast ExprBinary) {
        if !self.in_function {
            return;
        }

        let is_arithmetic = matches!(
            expr.op,
            BinOp::Add(_)
                | BinOp::Sub(_)
                | BinOp::Mul(_)
                | BinOp::Div(_)
                | BinOp::AddAssign(_)
                | BinOp::SubAssign(_)
                | BinOp::MulAssign(_)
                | BinOp::DivAssign(_)
        );

        if !is_arithmetic {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // Skip if both sides are compile-time constants (literals or
        // SCREAMING_SNAKE_CASE const paths). The product/sum is fixed at compile
        // time and constant-folded by rustc, so it cannot overflow at runtime.
        if is_const_like(&expr.left) && is_const_like(&expr.right) {
            return;
        }

        // Skip if either side is a literal (e.g., x + 1, slot + 1)
        // These are low risk and produce many false positives
        if is_literal(&expr.left) || is_literal(&expr.right) {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // Skip floating-point arithmetic: f32/f64 cannot integer-overflow
        // (IEEE-754 saturates to +/-infinity), so the integer-overflow property
        // this detector protects is categorically inapplicable.
        if is_float_operand(&expr.left, &self.current_fn_float_params)
            || is_float_operand(&expr.right, &self.current_fn_float_params)
        {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        let line = span_to_line(&expr.op.span());
        let snippet = snippet_at_line(&self.ctx.source, line);

        // Check if the line uses checked_* methods
        if snippet.contains("checked_")
            || snippet.contains("saturating_")
            || snippet.contains("wrapping_")
        {
            return;
        }

        // Skip string concatenation (+ on strings, common FP)
        let expr_str = expr.to_token_stream().to_string();
        if expr_str.contains("to_owned")
            || expr_str.contains("to_string")
            || expr_str.contains("String")
            || expr_str.contains("str")
            || expr_str.contains("format")
            || snippet.contains("as_bytes")
            || snippet.contains("to_owned")
            || snippet.contains("String")
        {
            return;
        }

        // Skip if adding to array index or len-like calls (low risk)
        if snippet.contains(".len()") || snippet.contains("as usize") {
            return;
        }

        // Skip compile-time constant expressions (size_of, align_of, etc.)
        if expr_str.contains("size_of") || expr_str.contains("align_of") {
            return;
        }

        // Skip widening casts: (a as u128) * (b as u128) is safe
        if is_widening_cast(&expr.left) && is_widening_cast(&expr.right) {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // Skip if either operand involves a saturating_* call (already clamped)
        if expr_str.contains("saturating_") {
            syn::visit::visit_expr_binary(self, expr);
            return;
        }

        // Division cannot overflow (only divide-by-zero) — use Low confidence
        let is_division = matches!(expr.op, BinOp::Div(_) | BinOp::DivAssign(_));
        let confidence = if is_division {
            Confidence::Low
        } else {
            Confidence::Medium
        };

        self.findings.push(Finding {
            detector_id: "SOL-003".to_string(),
            name: "integer-overflow".to_string(),
            severity: Severity::Critical,
            confidence,
            message: format!(
                "Unchecked arithmetic operation: {}",
                expr.to_token_stream().to_string()
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&expr.op.span()),
            snippet,
            recommendation: "Use checked_add(), checked_sub(), checked_mul(), or checked_div() to prevent overflow/underflow".to_string(),
            chain: Chain::Solana,
        });

        syn::visit::visit_expr_binary(self, expr);
    }
}

fn is_literal(expr: &Expr) -> bool {
    matches!(expr, Expr::Lit(_))
}

/// Check whether an identifier is written in SCREAMING_SNAKE_CASE — the
/// universal Rust convention for `const`/`static` compile-time constants.
fn is_screaming_snake(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        && s.chars().any(|c| c.is_ascii_uppercase())
}

/// Check if an expression is a compile-time constant: a literal, or a path
/// whose final segment is a SCREAMING_SNAKE_CASE const (e.g. `SECONDS_PER_DAY`).
/// Runtime variables use lower_snake_case, so this never masks variable
/// arithmetic — only both-const operands are treated as safe by the caller.
fn is_const_like(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(_) => true,
        Expr::Path(p) => p
            .path
            .segments
            .last()
            .map(|seg| is_screaming_snake(&seg.ident.to_string()))
            .unwrap_or(false),
        Expr::Paren(p) => is_const_like(&p.expr),
        Expr::Cast(c) => is_const_like(&c.expr),
        Expr::Group(g) => is_const_like(&g.expr),
        _ => false,
    }
}

/// Check if expression is a widening cast like `(x as u128)` or `x as u64`
fn is_widening_cast(expr: &Expr) -> bool {
    match expr {
        Expr::Cast(cast) => {
            let ty_str = cast.ty.to_token_stream().to_string();
            ty_str == "u128" || ty_str == "i128" || ty_str == "u64" || ty_str == "i64"
        }
        Expr::Paren(paren) => is_widening_cast(&paren.expr),
        _ => {
            // Also check token stream for "as u128" pattern as fallback
            let s = expr.to_token_stream().to_string();
            s.contains("as u128") || s.contains("as i128")
        }
    }
}

/// Collect the names of the current function's parameters whose declared type
/// is a floating-point type (f32/f64).
fn float_params_of_sig(sig: &syn::Signature) -> Vec<String> {
    let mut params = Vec::new();
    for input in &sig.inputs {
        if let syn::FnArg::Typed(pt) = input {
            let ty = pt.ty.to_token_stream().to_string();
            if ty.contains("f64") || ty.contains("f32") {
                if let syn::Pat::Ident(pi) = pt.pat.as_ref() {
                    params.push(pi.ident.to_string());
                }
            }
        }
    }
    params
}

/// Check if an operand is floating-point: a float literal, an `as f32`/`as f64`
/// cast, or a reference to a float-typed parameter of the enclosing function.
fn is_float_operand(expr: &Expr, float_params: &[String]) -> bool {
    match expr {
        Expr::Lit(lit) => matches!(&lit.lit, syn::Lit::Float(_)),
        Expr::Path(p) => p
            .path
            .get_ident()
            .map(|id| {
                let s = id.to_string();
                float_params.iter().any(|f| f == &s)
            })
            .unwrap_or(false),
        Expr::Cast(c) => {
            let ty = c.ty.to_token_stream().to_string();
            ty == "f64" || ty == "f32" || is_float_operand(&c.expr, float_params)
        }
        Expr::Paren(p) => is_float_operand(&p.expr, float_params),
        Expr::Group(g) => is_float_operand(&g.expr, float_params),
        Expr::Reference(r) => is_float_operand(&r.expr, float_params),
        Expr::Unary(u) => is_float_operand(&u.expr, float_params),
        Expr::MethodCall(m) => is_float_operand(&m.receiver, float_params),
        Expr::Binary(b) => {
            is_float_operand(&b.left, float_params) || is_float_operand(&b.right, float_params)
        }
        _ => false,
    }
}

/// Decide whether a function's arithmetic is guarded by input validation.
/// Combines the original macro/min-max string checks with two additional
/// idiomatic patterns:
///   * an `if <comparison> { return Err(..)/panic!(..) }` early-return guard, and
///   * delegation of validation to a resolvable helper called with `?`/unwrap.
fn fn_has_bounds_check(body_src: &str, block: &syn::Block, ast: &syn::File) -> bool {
    let string_guard = body_src.contains("assert !")
        || body_src.contains("assert_eq !")
        || body_src.contains("assert_ne !")
        || body_src.contains("require !")
        || body_src.contains("ensure !")
        || body_src.contains("min (")
        || body_src.contains(". min (")
        || body_src.contains(". max (")
        || body_src.contains("clamp");
    if string_guard {
        return true;
    }

    // Idiomatic native-Solana guard: `if amount > balance { return Err(..) }`.
    if has_if_comparison_guard(block) {
        return true;
    }

    // Validation factored into a helper (`check_*`/`validate_*`/…) that is
    // invoked with `?` (or unwrap/expect) so its bail-out dominates the
    // arithmetic. The helper's body is resolved from the crate AST and must
    // actually contain a validation construct — no blanket name-based skip.
    if body_delegates_validation(block, ast) {
        return true;
    }

    false
}

/// Walk `block` for an `if` whose condition contains a comparison and whose
/// then-branch diverges (returns / errors / panics). This is the standard
/// native-Solana bounds guard that cannot use Anchor's `require!`.
fn has_if_comparison_guard(block: &syn::Block) -> bool {
    struct GuardVisitor {
        found: bool,
    }
    impl<'ast> Visit<'ast> for GuardVisitor {
        fn visit_expr_if(&mut self, node: &'ast syn::ExprIf) {
            if expr_has_comparison(&node.cond) && branch_bails(&node.then_branch) {
                self.found = true;
            }
            syn::visit::visit_expr_if(self, node);
        }
    }
    let mut v = GuardVisitor { found: false };
    v.visit_block(block);
    v.found
}

/// True if the expression tree contains a comparison binary operator.
fn expr_has_comparison(expr: &Expr) -> bool {
    struct CmpVisitor {
        found: bool,
    }
    impl<'ast> Visit<'ast> for CmpVisitor {
        fn visit_expr_binary(&mut self, node: &'ast ExprBinary) {
            if matches!(
                node.op,
                BinOp::Lt(_)
                    | BinOp::Gt(_)
                    | BinOp::Le(_)
                    | BinOp::Ge(_)
                    | BinOp::Eq(_)
                    | BinOp::Ne(_)
            ) {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, node);
        }
    }
    let mut v = CmpVisitor { found: false };
    v.visit_expr(expr);
    v.found
}

/// True if the (short-circuit) branch block diverges — returns, produces an
/// `Err`, panics, or bails. Scoped to the branch so it cannot be confused with
/// unrelated code elsewhere in the function.
fn branch_bails(block: &syn::Block) -> bool {
    let s = block.to_token_stream().to_string();
    s.contains("return")
        || s.contains("Err")
        || s.contains("panic")
        || s.contains("bail")
        || s.contains("require")
        || s.contains("ensure")
}

/// True if `block` propagates the result of a validating helper via `?` or
/// unwrap/expect, where the helper is resolvable in `ast` and its body actually
/// performs a validation. This is a sound, resolution-based check — a helper
/// call whose body we cannot resolve, or that does not validate, is NOT skipped.
fn body_delegates_validation(block: &syn::Block, ast: &syn::File) -> bool {
    struct DelegationVisitor {
        targets: Vec<String>,
    }
    impl<'ast> Visit<'ast> for DelegationVisitor {
        fn visit_expr_try(&mut self, node: &'ast syn::ExprTry) {
            if let Some(name) = call_target_name(&node.expr) {
                self.targets.push(name);
            }
            syn::visit::visit_expr_try(self, node);
        }
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            let m = node.method.to_string();
            if m == "unwrap" || m == "expect" {
                if let Some(name) = call_target_name(&node.receiver) {
                    self.targets.push(name);
                }
            }
            syn::visit::visit_expr_method_call(self, node);
        }
    }

    let mut v = DelegationVisitor {
        targets: Vec::new(),
    };
    v.visit_block(block);

    v.targets.iter().any(|name| fn_validates_input(ast, name))
}

/// Extract the callee name of a direct call expression, if any.
fn call_target_name(expr: &Expr) -> Option<String> {
    if let Expr::Call(call) = expr {
        if let Expr::Path(p) = call.func.as_ref() {
            if let Some(seg) = p.path.segments.last() {
                return Some(seg.ident.to_string());
            }
        }
    }
    None
}

/// Resolve a function/method named `name` in the crate AST and report whether
/// its body actually performs input validation (assert/require/ensure macros or
/// an if-comparison early-return guard).
fn fn_validates_input(ast: &syn::File, name: &str) -> bool {
    for item in &ast.items {
        match item {
            syn::Item::Fn(f) if f.sig.ident == name => {
                if block_has_validation(&f.block) {
                    return true;
                }
            }
            syn::Item::Impl(imp) => {
                for it in &imp.items {
                    if let syn::ImplItem::Fn(m) = it {
                        if m.sig.ident == name && block_has_validation(&m.block) {
                            return true;
                        }
                    }
                }
            }
            syn::Item::Mod(m) => {
                if let Some((_, items)) = &m.content {
                    for inner in items {
                        if let syn::Item::Fn(f) = inner {
                            if f.sig.ident == name && block_has_validation(&f.block) {
                                return true;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
    false
}

/// True if a resolved helper body contains a real validation construct.
fn block_has_validation(block: &syn::Block) -> bool {
    let s = block.to_token_stream().to_string();
    s.contains("assert !")
        || s.contains("assert_eq !")
        || s.contains("assert_ne !")
        || s.contains("require !")
        || s.contains("ensure !")
        || has_if_comparison_guard(block)
}

/// Check if function name indicates a fee/swap/math calculation helper
/// These functions exist specifically to do arithmetic and typically have
/// pre-validated inputs or return Results for overflow.
fn is_math_helper_fn(name: &str) -> bool {
    let n = name.to_lowercase();
    n.contains("_fee")
        || n.contains("fee_")
        || n.starts_with("calculate")
        || n.starts_with("compute")
        || n.starts_with("convert")
        || n.contains("swap")
        || n.contains("curve")
        || n.contains("interpolat")
        || n.contains("_amount")
        || n.contains("amount_")
        || n.contains("_rate")
        || n.contains("rate_")
        || n.contains("_price")
        || n.contains("price_")
        || n == "ceil_div"
        || n == "floor_div"
}

/// Check if function name indicates a Pack/serialization impl
fn is_pack_fn(name: &str) -> bool {
    let n = name.to_lowercase();
    n == "pack_into_slice"
        || n == "unpack_from_slice"
        || n == "pack"
        || n == "unpack"
        || n == "serialize"
        || n == "deserialize"
        || n == "try_from_slice"
        || n.starts_with("pack_")
        || n.starts_with("unpack_")
}

/// Check if function is a test
fn is_test_fn(name: &str, attrs: &[syn::Attribute]) -> bool {
    let n = name.to_lowercase();
    if n.starts_with("test_") || n.ends_with("_test") || n.contains("_works") {
        return true;
    }
    has_attribute(attrs, "test")
}

use proc_macro2::Span;

trait SpanExt {
    fn span(&self) -> Span;
}

impl SpanExt for BinOp {
    fn span(&self) -> Span {
        match self {
            BinOp::Add(t) => t.span,
            BinOp::Sub(t) => t.span,
            BinOp::Mul(t) => t.span,
            BinOp::Div(t) => t.span,
            BinOp::AddAssign(t) => t.spans[0],
            BinOp::SubAssign(t) => t.spans[0],
            BinOp::MulAssign(t) => t.spans[0],
            BinOp::DivAssign(t) => t.spans[0],
            _ => Span::call_site(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::call_graph::build_call_graph;

    fn run_detector(source: &str) -> Vec<Finding> {
        // Prepend Solana marker so detector recognizes file as Solana code
        let full_source = format!("use solana_program::pubkey::Pubkey;\n{}", source);
        let ast = syn::parse_file(&full_source).unwrap();
        let ctx = ScanContext::new(
            std::path::PathBuf::from("test.rs"),
            full_source,
            ast,
            Chain::Solana,
            std::collections::HashMap::new(),
        );
        IntegerOverflowDetector.detect(&ctx)
    }

    /// Same as `run_detector` but populates the per-file call graph exactly as
    /// the production scanner does, so call-graph-dependent logic is exercised.
    fn run_detector_with_graph(source: &str) -> Vec<Finding> {
        let full_source = format!("use solana_program::pubkey::Pubkey;\n{}", source);
        let ast = syn::parse_file(&full_source).unwrap();
        let graph = build_call_graph(&ast);
        let ctx = ScanContext::new(
            std::path::PathBuf::from("test.rs"),
            full_source,
            ast,
            Chain::Solana,
            graph,
        );
        IntegerOverflowDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unchecked_arithmetic() {
        let source = r#"
            fn transfer(amount: u64, fee: u64) -> u64 {
                let total = amount + fee;
                total
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect unchecked arithmetic");
    }

    #[test]
    fn test_no_finding_for_string_concat() {
        let source = r#"
            fn build_name(prefix: String, suffix: &str) -> String {
                let result = prefix.to_owned() + suffix;
                result
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag string concatenation");
    }

    #[test]
    fn test_no_finding_literal_add() {
        let source = r#"
            fn next_slot(slot: u64) -> u64 {
                let next = slot + 1;
                next
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag adding a literal constant"
        );
    }

    #[test]
    fn test_no_finding_for_literals() {
        let source = r#"
            fn constants() -> u64 {
                let x = 1 + 2;
                x
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag literal arithmetic");
    }

    #[test]
    fn test_no_finding_widening_cast() {
        let source = r#"
            fn safe_multiply(a: u64, b: u64) -> u128 {
                let result = (a as u128) * (b as u128);
                result
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag widening cast multiplication"
        );
    }

    #[test]
    fn test_no_finding_pack_fn() {
        let source = r#"
            fn pack_into_slice(&self, dst: &mut [u8]) {
                let offset = start + size;
                dst[offset] = self.value;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag pack/serialization functions"
        );
    }

    #[test]
    fn test_no_finding_fee_calculator() {
        let source = r#"
            fn calculate_fee(amount: u64, fee_bps: u64) -> u64 {
                let fee = amount * fee_bps / BPS_DENOMINATOR;
                fee
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag fee/swap calculator functions"
        );
    }

    #[test]
    fn test_no_finding_with_assert_guard() {
        let source = r#"
            fn withdraw(balance: u64, amount: u64) -> u64 {
                assert!(amount <= balance);
                let remaining = balance - amount;
                remaining
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag arithmetic guarded by assert"
        );
    }

    #[test]
    fn test_division_low_confidence() {
        let source = r#"
            fn split_reward(amount: u64, total: u64) -> u64 {
                let share = amount / total;
                share
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should still detect division");
        assert_eq!(
            findings[0].confidence,
            Confidence::Low,
            "Division should have Low confidence"
        );
    }

    // --- FP-elimination regression tests -----------------------------------

    /// FP idx 0: an `if amount > balance { return Err(..) }` early-return guard
    /// dominates the subtraction, so it can never underflow.
    #[test]
    fn test_no_finding_if_comparison_early_return_guard() {
        let source = r#"
            use solana_program::program_error::ProgramError;

            pub fn withdraw(balance: u64, amount: u64) -> Result<u64, ProgramError> {
                if amount > balance {
                    return Err(ProgramError::InsufficientFunds);
                }
                Ok(balance - amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag subtraction guarded by an if/return-Err comparison"
        );
    }

    /// Sanity: the same shape WITHOUT any guard must still fire (no false negative).
    #[test]
    fn test_still_fires_without_guard() {
        let source = r#"
            use solana_program::program_error::ProgramError;

            pub fn withdraw(balance: u64, amount: u64) -> Result<u64, ProgramError> {
                Ok(balance - amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Unguarded subtraction must still be flagged"
        );
    }

    /// FP idx 2: validation delegated to a `check_*` helper invoked with `?`.
    #[test]
    fn test_no_finding_delegated_validation_helper() {
        let source = r#"
            use solana_program::program_error::ProgramError;

            fn check_withdraw(balance: u64, amount: u64) -> Result<(), ProgramError> {
                require!(amount <= balance, ProgramError::InsufficientFunds);
                Ok(())
            }

            pub fn withdraw(balance: u64, amount: u64) -> Result<u64, ProgramError> {
                check_withdraw(balance, amount)?;
                Ok(balance - amount)
            }
        "#;
        let findings = run_detector_with_graph(source);
        assert!(
            findings.is_empty(),
            "Should not flag arithmetic when validation is delegated to a resolvable helper"
        );
    }

    /// Sanity: a helper that does NOT validate must not suppress the finding.
    #[test]
    fn test_still_fires_when_helper_does_not_validate() {
        let source = r#"
            use solana_program::program_error::ProgramError;

            fn log_withdraw(balance: u64, amount: u64) -> Result<(), ProgramError> {
                Ok(())
            }

            pub fn withdraw(balance: u64, amount: u64) -> Result<u64, ProgramError> {
                log_withdraw(balance, amount)?;
                Ok(balance - amount)
            }
        "#;
        let findings = run_detector_with_graph(source);
        assert!(
            !findings.is_empty(),
            "Delegation to a non-validating helper must still be flagged"
        );
    }

    /// FP idx 3: non-#[test] helper inside a `#[cfg(test)]` module.
    #[test]
    fn test_no_finding_cfg_test_module_helper() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                fn seed_balances(a: u64, b: u64) -> u64 {
                    a + b
                }

                #[test]
                fn deposits_accumulate() {
                    assert_eq!(seed_balances(1, 2), 3);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag helpers inside #[cfg(test)] modules"
        );
    }

    /// FP idx 4: arithmetic on two named SCREAMING_SNAKE_CASE constants.
    #[test]
    fn test_no_finding_const_path_arithmetic() {
        let source = r#"
            use solana_program::clock::Clock;

            const SECONDS_PER_DAY: i64 = 86_400;
            const LOCK_DAYS: i64 = 30;

            pub fn lock_duration() -> i64 {
                SECONDS_PER_DAY * LOCK_DAYS
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag arithmetic on two compile-time const paths"
        );
    }

    /// Sanity: a const multiplied by a runtime variable must still fire.
    #[test]
    fn test_still_fires_const_times_variable() {
        let source = r#"
            const SCALE: u64 = 1_000_000;

            pub fn apply_scale(n: u64) -> u64 {
                SCALE * n
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "const * runtime variable can overflow and must still be flagged"
        );
    }

    /// FP idx 5: floating-point multiplication cannot integer-overflow.
    #[test]
    fn test_no_finding_float_arithmetic() {
        let source = r#"
            // off-chain client util in the same crate
            pub fn ui_token_value(ui_amount: f64, usd_quote: f64) -> f64 {
                ui_amount * usd_quote
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag floating-point arithmetic"
        );
    }

    /// Sanity: integer arithmetic in a fn that also has a float param must fire.
    #[test]
    fn test_still_fires_integer_arith_alongside_float_param() {
        let source = r#"
            pub fn mixed(price: f64, a: u64, b: u64) -> u64 {
                a + b
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Integer overflow on u64 operands must still fire even with a float param present"
        );
    }
}
