use quote::ToTokens;
use syn::visit::Visit;
use syn::{Expr, ItemFn};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct DuplicateMutableAccountsDetector;

impl Detector for DuplicateMutableAccountsDetector {
    fn id(&self) -> &'static str {
        "SOL-019"
    }
    fn name(&self) -> &'static str {
        "duplicate-mutable-accounts"
    }
    fn description(&self) -> &'static str {
        "Detects functions with multiple mutable AccountInfo params without key uniqueness check"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
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
        let mut visitor = DuplicateMutableVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct DuplicateMutableVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// Names of methods that perform a mutable borrow of account data / lamports.
const MUT_BORROW_METHODS: &[&str] = &[
    "try_borrow_mut_data",
    "try_borrow_mut_lamports",
    "try_borrow_mut",
    "borrow_mut",
];

/// Returns true if a function's own body source contains a recognized
/// key-uniqueness check.
///
/// Note: tokenized source uses spaces (e.g., "! =" for "!=") and macros have a
/// space before ! (e.g., "assert_ne !"). Two idioms are accepted:
///   1. Inequality assertions / macros (`a.key != b.key`, `assert_ne!`,
///      `require_keys_neq!`, `require_neq!`, ...).
///   2. An equality comparison used as a bail-out
///      (`if a.key == b.key { return Err(..) }` / `a.key.eq(&b.key)` guard).
fn body_has_key_check(body_src: &str) -> bool {
    let has_inequality = body_src.contains("key !=")
        || body_src.contains("key ! =")
        || body_src.contains("key () !=")
        || body_src.contains("key () ! =")
        || body_src.contains("key() !=")
        || body_src.contains("!= key")
        || body_src.contains("! = key")
        || body_src.contains("require_keys_neq")
        || body_src.contains("require_neq")
        || body_src.contains("assert_ne")
        || body_src.contains("require_keys_eq");

    if has_inequality {
        return true;
    }

    // Equality-guard idiom: an equality comparison of keys that bails out with an
    // error. This is the canonical native-Solana mitigation
    // (`if from.key == to.key { return Err(..) }`). Require an accompanying error
    // bail-out so a stray `==` in unrelated code does not count.
    let has_bail = body_src.contains("return Err") || body_src.contains("Err (");
    if !has_bail {
        return false;
    }
    body_src.contains("key ==")
        || body_src.contains("key () ==")
        || body_src.contains("== key")
        || body_src.contains("key . eq (")
        || body_src.contains("key () . eq (")
}

/// Extract the leading (base) identifier of an expression, peeling off field
/// accesses, method calls, references, parens, unary ops and `?`.
///
/// e.g. `from` -> "from", `from.data` -> "from", `from.lamports.borrow_mut()`
/// receiver `from.lamports` -> "from", `&from` -> "from".
fn base_ident(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(p) => p
            .path
            .get_ident()
            .map(|i| i.to_string())
            .or_else(|| p.path.segments.last().map(|s| s.ident.to_string())),
        Expr::Field(f) => base_ident(&f.base),
        Expr::MethodCall(m) => base_ident(&m.receiver),
        Expr::Reference(r) => base_ident(&r.expr),
        Expr::Paren(p) => base_ident(&p.expr),
        Expr::Group(g) => base_ident(&g.expr),
        Expr::Unary(u) => base_ident(&u.expr),
        Expr::Try(t) => base_ident(&t.expr),
        Expr::Index(i) => base_ident(&i.expr),
        _ => None,
    }
}

/// Names of the `&AccountInfo`-typed parameters of a function (in order).
fn account_info_params(func: &ItemFn) -> Vec<String> {
    func.sig
        .inputs
        .iter()
        .filter_map(|arg| {
            if let syn::FnArg::Typed(pt) = arg {
                let ty_str = pt.ty.to_token_stream().to_string();
                if ty_str.contains("AccountInfo") {
                    if let syn::Pat::Ident(pi) = pt.pat.as_ref() {
                        return Some(pi.ident.to_string());
                    }
                }
            }
            None
        })
        .collect()
}

/// Distinct AccountInfo parameter names that are actually mutably borrowed
/// inside the function body (data or lamports). Mutable borrows on unrelated
/// values (e.g. a local `RefCell`) are excluded because their base identifier
/// is not one of the account parameters.
fn mutated_account_params(func: &ItemFn, account_params: &[String]) -> Vec<String> {
    let mut collector = MethodCallCollector { calls: Vec::new() };
    collector.visit_block(&func.block);

    let mut mutated: Vec<String> = Vec::new();
    for call in &collector.calls {
        let method = call.method.to_string();
        if !MUT_BORROW_METHODS.iter().any(|m| *m == method) {
            continue;
        }
        if let Some(base) = base_ident(&call.receiver) {
            if account_params.iter().any(|p| *p == base) && !mutated.contains(&base) {
                mutated.push(base);
            }
        }
    }
    mutated
}

/// Find a top-level `fn` item by name in the parsed file.
fn find_top_level_fn<'b>(ast: &'b syn::File, name: &str) -> Option<&'b ItemFn> {
    ast.items.iter().find_map(|it| match it {
        syn::Item::Fn(f) if f.sig.ident == name => Some(f),
        _ => None,
    })
}

/// Collect all plain (path) call expressions inside a function body.
struct CallExprCollector {
    calls: Vec<syn::ExprCall>,
}

impl<'ast> Visit<'ast> for CallExprCollector {
    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        self.calls.push(node.clone());
        syn::visit::visit_expr_call(self, node);
    }
}

/// Sound call-graph resolution for a key check delegated to a helper.
///
/// Returns true only when `func` calls a helper that is RESOLVABLE in this same
/// file, whose body genuinely contains a key-uniqueness check, AND that call
/// passes at least two of `func`'s AccountInfo parameters as arguments. This
/// avoids a name-based blanket skip: we confirm the actual check tokens in the
/// resolved callee body and that the relevant accounts flow into it.
fn resolves_key_check_via_helper(
    func: &ItemFn,
    ast: &syn::File,
    account_params: &[String],
) -> bool {
    let mut collector = CallExprCollector { calls: Vec::new() };
    collector.visit_block(&func.block);

    for call in &collector.calls {
        let callee_name = match call.func.as_ref() {
            Expr::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
            _ => None,
        };
        let Some(callee_name) = callee_name else {
            continue;
        };

        let Some(helper) = find_top_level_fn(ast, &callee_name) else {
            continue;
        };
        if helper.sig.ident == func.sig.ident {
            continue; // ignore trivial self-recursion
        }

        if !body_has_key_check(&fn_body_source(helper)) {
            continue;
        }

        // Require >= 2 distinct account params passed into the checking helper.
        let mut passed: Vec<String> = Vec::new();
        for arg in &call.args {
            if let Some(id) = base_ident(arg) {
                if account_params.iter().any(|p| *p == id) && !passed.contains(&id) {
                    passed.push(id);
                }
            }
        }
        if passed.len() >= 2 {
            return true;
        }
    }
    false
}

/// Returns true if the function is a test function (`#[test]`, `#[tokio::test]`,
/// `#[ink::test]`, ...) or has a name containing "test".
fn is_test_fn(func: &ItemFn) -> bool {
    if func.sig.ident.to_string().contains("test") {
        return true;
    }
    func.attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

impl<'ast, 'a> Visit<'ast> for DuplicateMutableVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        // Skip `#[cfg(test)]` modules entirely — they encode tests, not
        // production instruction handlers.
        if has_attribute_with_value(&module.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        if is_test_fn(func) {
            return;
        }

        let fn_src = func.to_token_stream().to_string();

        // Skip Anchor Context<T> patterns — Anchor validates key uniqueness
        if fn_src.contains("Context <") || fn_src.contains("Context<") {
            return;
        }

        // Collect the AccountInfo-typed parameters.
        let account_params = account_info_params(func);
        if account_params.len() < 2 {
            return;
        }

        // Require that at least TWO distinct account parameters are actually
        // mutably borrowed. The duplicate-mutable-accounts attack needs two
        // mutable aliases whose writes interfere; a single writable account (or
        // a `borrow_mut` on an unrelated local) poses no aliased-write hazard.
        let mutated = mutated_account_params(func, &account_params);
        if mutated.len() < 2 {
            return;
        }

        let body_src = fn_body_source(func);

        // Key-uniqueness check present in this function's own body?
        if body_has_key_check(&body_src) {
            return;
        }

        // Or delegated to a resolvable helper that performs the check?
        if resolves_key_check_via_helper(func, &self.ctx.ast, &account_params) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-019".to_string(),
            name: "duplicate-mutable-accounts".to_string(),
            severity: Severity::High,
            confidence: Confidence::Medium,
            message: format!(
                "Function '{}' has {} AccountInfo params with mutable access but no key uniqueness assertion",
                func.sig.ident, account_params.len()
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Assert that account keys are not equal (e.g., require_keys_neq! or assert_ne!(a.key, b.key)) to prevent duplicate mutable account attacks, or use Anchor's Context<T>".to_string(),
            chain: Chain::Solana,
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
            Chain::Solana,
            std::collections::HashMap::new(),
        );
        DuplicateMutableAccountsDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_duplicate_mutable_no_check() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn transfer(from: &AccountInfo, to: &AccountInfo) {
                let mut from_data = from.try_borrow_mut_data()?;
                let mut to_data = to.try_borrow_mut_data()?;
                from_data[0] -= 1;
                to_data[0] += 1;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect duplicate mutable accounts without key check"
        );
    }

    #[test]
    fn test_no_finding_with_key_check() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn transfer(from: &AccountInfo, to: &AccountInfo) {
                assert_ne!(from.key, to.key);
                let mut from_data = from.try_borrow_mut_data()?;
                let mut to_data = to.try_borrow_mut_data()?;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with key uniqueness assertion"
        );
    }

    #[test]
    fn test_no_finding_single_account() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn update(account: &AccountInfo) {
                let mut data = account.try_borrow_mut_data()?;
                data[0] = 1;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag single AccountInfo param"
        );
    }

    #[test]
    fn test_skips_anchor_context() {
        let source = r#"
            use anchor_lang::prelude::*;
            fn transfer(ctx: Context<Transfer>, from: &AccountInfo, to: &AccountInfo) {
                let mut from_data = from.try_borrow_mut_data()?;
                let mut to_data = to.try_borrow_mut_data()?;
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should skip Anchor Context patterns");
    }

    // --- Regression tests: false positives that must NOT be flagged ---

    // FP idx 0: equality guard with early return.
    #[test]
    fn test_no_finding_equality_guard_early_return() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::program_error::ProgramError;
            use solana_program::entrypoint::ProgramResult;

            fn transfer(from: &AccountInfo, to: &AccountInfo) -> ProgramResult {
                if from.key == to.key {
                    return Err(ProgramError::InvalidArgument);
                }
                let mut from_data = from.try_borrow_mut_data()?;
                let mut to_data = to.try_borrow_mut_data()?;
                from_data[0] -= 1;
                to_data[0] += 1;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Equality guard with early Err return should be recognized as a key check"
        );
    }

    // FP idx 1: only one of the AccountInfo params is ever mutated.
    #[test]
    fn test_no_finding_single_mutated_param() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::program_error::ProgramError;
            use solana_program::entrypoint::ProgramResult;

            fn set_config_value(config: &AccountInfo, authority: &AccountInfo, value: u8) -> ProgramResult {
                if !authority.is_signer {
                    return Err(ProgramError::MissingRequiredSignature);
                }
                let mut data = config.try_borrow_mut_data()?;
                data[0] = value;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Only one account is mutated; no aliased-write hazard"
        );
    }

    // FP idx 2: key check factored into a helper called with both params.
    #[test]
    fn test_no_finding_key_check_in_helper() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::program_error::ProgramError;
            use solana_program::entrypoint::ProgramResult;

            fn assert_distinct(a: &AccountInfo, b: &AccountInfo) -> ProgramResult {
                assert_ne!(a.key, b.key);
                Ok(())
            }

            fn transfer(from: &AccountInfo, to: &AccountInfo) -> ProgramResult {
                assert_distinct(from, to)?;
                let mut from_data = from.try_borrow_mut_data()?;
                let mut to_data = to.try_borrow_mut_data()?;
                from_data[0] -= 1;
                to_data[0] += 1;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Key check delegated to a resolvable helper should suppress the finding"
        );
    }

    // Soundness guard for FP idx 2: an unrelated helper that does NOT check the
    // flagged accounts must NOT suppress a genuine finding.
    #[test]
    fn test_helper_without_check_still_fires() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;

            fn log_it(a: &AccountInfo, b: &AccountInfo) -> ProgramResult {
                Ok(())
            }

            fn transfer(from: &AccountInfo, to: &AccountInfo) -> ProgramResult {
                log_it(from, to)?;
                let mut from_data = from.try_borrow_mut_data()?;
                let mut to_data = to.try_borrow_mut_data()?;
                from_data[0] -= 1;
                to_data[0] += 1;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A helper without a key check must not suppress the finding"
        );
    }

    // FP idx 3: Anchor's require_neq! (non-keys variant).
    #[test]
    fn test_no_finding_require_neq() {
        let source = r#"
            use anchor_lang::prelude::*;

            fn settle_pair(a: &AccountInfo, b: &AccountInfo) -> Result<()> {
                require_neq!(a.key(), b.key(), ErrorCode::DuplicateAccount);
                let mut da = a.try_borrow_mut_data()?;
                let mut db = b.try_borrow_mut_data()?;
                da[0] = 1;
                db[0] = 2;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "require_neq! should be recognized as a key uniqueness check"
        );
    }

    // FP idx 4: borrow_mut on a non-account local value.
    #[test]
    fn test_no_finding_borrow_mut_on_non_account() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use std::cell::RefCell;

            fn record_pair(a: &AccountInfo, b: &AccountInfo, log: &RefCell<Vec<u8>>) {
                let mut buf = log.borrow_mut();
                buf.extend_from_slice(a.key.as_ref());
                buf.extend_from_slice(b.key.as_ref());
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "borrow_mut on an unrelated RefCell must not count as account mutation"
        );
    }

    // Real-bug shape via lamports mutation must still fire.
    #[test]
    fn test_detects_lamports_mutation_no_check() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;

            fn move_lamports(from: &AccountInfo, to: &AccountInfo, amount: u64) -> ProgramResult {
                **from.lamports.borrow_mut() -= amount;
                **to.lamports.borrow_mut() += amount;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Two accounts mutated via lamports with no key check should fire"
        );
    }
}
