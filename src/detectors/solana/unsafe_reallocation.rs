use quote::ToTokens;
use syn::visit::Visit;
use syn::{FnArg, GenericArgument, ItemFn, ItemMod, PathArguments, Type};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnsafeReallocationDetector;

impl Detector for UnsafeReallocationDetector {
    fn id(&self) -> &'static str {
        "SOL-018"
    }
    fn name(&self) -> &'static str {
        "unsafe-account-reallocation"
    }
    fn description(&self) -> &'static str {
        "Detects .realloc() calls without signer and rent/lamport checks"
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
        // Pre-compute a light call graph over the file's top-level functions so we
        // can recognise the "checks live in the caller" helper-factoring pattern.
        let fns = collect_fn_data(&ctx.ast);
        let mut visitor = ReallocVisitor {
            findings: &mut findings,
            ctx,
            fns,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Which required check a helper may be relying on its callers to perform.
#[derive(Clone, Copy)]
enum NeededCheck {
    Signer,
    Rent,
}

/// Minimal per-function summary used for caller-side check propagation.
struct FnData {
    name: String,
    has_signer: bool,
    has_rent: bool,
    calls: Vec<String>,
}

struct ReallocVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    fns: Vec<FnData>,
}

impl<'ast, 'a> Visit<'ast> for ReallocVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // FP: helper functions inside a #[cfg(test)] module are compiled only for
        // tests and never ship on-chain. Skip the whole module (do not recurse).
        if has_nested_attribute(&module.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        if fn_name.contains("test") || has_attribute(&func.attrs, "test") {
            return;
        }

        let fn_src = func.to_token_stream().to_string();

        // Skip Anchor #[account(realloc = ...)] patterns
        // Tokenized form: # [account (...realloc =...)]
        if fn_src.contains("realloc =") || fn_src.contains("realloc=") {
            if fn_src.contains("# [account")
                || fn_src.contains("#[account")
                || fn_src.contains("account (")
            {
                return;
            }
        }

        // Locate .realloc() method calls via the AST. AccountInfo::realloc always
        // takes exactly two arguments (new_len, zero_init). Requiring that shape
        // avoids flagging custom single-argument buffer/allocator wrappers that
        // merely happen to expose a method called `realloc`.
        let mut mc = MethodCallCollector { calls: Vec::new() };
        mc.visit_block(&func.block);
        let has_account_realloc = mc
            .calls
            .iter()
            .any(|c| c.method == "realloc" && c.args.len() == 2);
        if !has_account_realloc {
            return;
        }

        let body_src = fn_body_source(func);

        let mut has_signer_check = source_has_signer(&body_src);
        let mut has_rent_check = source_has_rent(&body_src);

        // FP: Anchor handlers enforce the signer via a `Signer<'info>` field (or a
        // has_one binding) in the #[derive(Accounts)] struct named by the handler's
        // `Context<T>` parameter — that constraint runs during account
        // deserialization, before the body, so it is invisible to a body-only scan.
        if !has_signer_check && context_struct_enforces_signer(&self.ctx.ast, func) {
            has_signer_check = true;
        }

        // FP: the required checks may live in a caller that delegates the raw
        // realloc to this private helper. Only trust a caller we can actually
        // resolve in the call graph that both calls this function and performs the
        // check — never a blanket name-based skip.
        if !has_signer_check && caller_provides(&self.fns, &fn_name, NeededCheck::Signer) {
            has_signer_check = true;
        }
        if !has_rent_check && caller_provides(&self.fns, &fn_name, NeededCheck::Rent) {
            has_rent_check = true;
        }

        if !has_signer_check || !has_rent_check {
            let line = span_to_line(&func.sig.ident.span());
            let mut missing = Vec::new();
            if !has_signer_check {
                missing.push("signer check");
            }
            if !has_rent_check {
                missing.push("rent/lamport check");
            }
            self.findings.push(Finding {
                detector_id: "SOL-018".to_string(),
                name: "unsafe-account-reallocation".to_string(),
                severity: Severity::High,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' calls .realloc() without {}",
                    func.sig.ident,
                    missing.join(" and ")
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Verify the caller is a signer and ensure rent exemption is maintained after reallocation, or use Anchor's #[account(realloc = ...)]".to_string(),
                chain: Chain::Solana,
            });
        }
    }
}

/// Signer check heuristic. Case-insensitive on the word "signer" so that named
/// helper idioms (assert_signer, check_signer, require_signer!, validate_signer,
/// ...) as well as `is_signer` / `Signer<'info>` all count. A truly unchecked
/// realloc body contains no form of the word at all.
fn source_has_signer(src: &str) -> bool {
    src.to_lowercase().contains("signer")
}

/// Rent / lamport check heuristic (kept identical to the original tokens so real
/// detection is unchanged).
fn source_has_rent(src: &str) -> bool {
    src.contains("rent")
        || src.contains("Rent")
        || src.contains("lamport")
        || src.contains("minimum_balance")
}

/// Build a light summary of every top-level function in the file.
fn collect_fn_data(ast: &syn::File) -> Vec<FnData> {
    let mut out = Vec::new();
    for item in &ast.items {
        if let syn::Item::Fn(func) = item {
            let body = fn_body_source(func);
            let mut cc = CallNameCollector { names: Vec::new() };
            cc.visit_block(&func.block);
            out.push(FnData {
                name: func.sig.ident.to_string(),
                has_signer: source_has_signer(&body),
                has_rent: source_has_rent(&body),
                calls: cc.names,
            });
        }
    }
    out
}

const MAX_CALLER_DEPTH: usize = 6;

/// Returns true if some (transitive) caller of `target` that actually calls it
/// performs the needed check. Resolution is confined to functions we can see in
/// this file's call graph — an unresolved / unreachable helper stays flagged.
fn caller_provides(fns: &[FnData], target: &str, kind: NeededCheck) -> bool {
    let mut visited: Vec<String> = Vec::new();
    caller_provides_rec(fns, target, kind, &mut visited, 0)
}

fn caller_provides_rec(
    fns: &[FnData],
    target: &str,
    kind: NeededCheck,
    visited: &mut Vec<String>,
    depth: usize,
) -> bool {
    if depth >= MAX_CALLER_DEPTH {
        return false;
    }
    for f in fns {
        if f.name == target {
            continue;
        }
        if visited.contains(&f.name) {
            continue;
        }
        if !f.calls.iter().any(|c| c == target) {
            continue;
        }
        let has = match kind {
            NeededCheck::Signer => f.has_signer,
            NeededCheck::Rent => f.has_rent,
        };
        if has {
            return true;
        }
        visited.push(f.name.clone());
        if caller_provides_rec(fns, &f.name, kind, visited, depth + 1) {
            return true;
        }
    }
    false
}

/// Extract `T` from an Anchor handler parameter of type `Context<..., T>`.
fn context_generic_ident(func: &ItemFn) -> Option<String> {
    for input in &func.sig.inputs {
        if let FnArg::Typed(pt) = input {
            if let Type::Path(tp) = pt.ty.as_ref() {
                if let Some(seg) = tp.path.segments.last() {
                    if seg.ident == "Context" {
                        if let PathArguments::AngleBracketed(ab) = &seg.arguments {
                            let mut last_ty = None;
                            for arg in &ab.args {
                                if let GenericArgument::Type(Type::Path(inner)) = arg {
                                    if let Some(s) = inner.path.segments.last() {
                                        last_ty = Some(s.ident.to_string());
                                    }
                                }
                            }
                            return last_ty;
                        }
                    }
                }
            }
        }
    }
    None
}

/// Resolve the Accounts struct named by the handler's `Context<T>` and confirm it
/// enforces the signer via a `Signer` field or a `has_one` authority binding.
fn context_struct_enforces_signer(ast: &syn::File, func: &ItemFn) -> bool {
    let name = match context_generic_ident(func) {
        Some(n) => n,
        None => return false,
    };
    for item in &ast.items {
        if let syn::Item::Struct(s) = item {
            if s.ident == name {
                let src = s.to_token_stream().to_string();
                return src.contains("Signer") || src.contains("has_one");
            }
        }
    }
    false
}

/// Collect the names of functions/methods called within a block.
struct CallNameCollector {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for CallNameCollector {
    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if let syn::Expr::Path(p) = node.func.as_ref() {
            if let Some(seg) = p.path.segments.last() {
                self.names.push(seg.ident.to_string());
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        self.names.push(node.method.to_string());
        syn::visit::visit_expr_method_call(self, node);
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
        UnsafeReallocationDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_realloc_without_checks() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn resize_account(account: &AccountInfo) {
                account.realloc(new_size, false).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect realloc without signer and rent checks"
        );
    }

    #[test]
    fn test_no_finding_with_both_checks() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn resize_account(account: &AccountInfo, authority: &AccountInfo) {
                if !authority.is_signer {
                    return Err(ProgramError::MissingRequiredSignature);
                }
                let rent = Rent::get()?;
                let min_balance = rent.minimum_balance(new_size);
                account.realloc(new_size, false).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with signer + rent checks"
        );
    }

    #[test]
    fn test_detects_realloc_missing_signer_only() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn resize_account(account: &AccountInfo) {
                let rent = Rent::get()?;
                account.realloc(new_size, false).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect realloc missing signer check"
        );
        assert!(findings[0].message.contains("signer check"));
    }

    #[test]
    fn test_skips_anchor_realloc_attribute() {
        let source = r#"
            use anchor_lang::prelude::*;
            #[account(realloc = space)]
            fn process(ctx: Context<Resize>) {
                ctx.accounts.data.realloc(new_size, false).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should skip Anchor realloc attribute patterns"
        );
    }

    // ---- FP regression tests (should NOT flag) ----

    // idx 0: Anchor handler; signer enforced by Signer<'info> in the Accounts
    // struct named by the Context<T> parameter, manual realloc in the body.
    #[test]
    fn test_no_finding_anchor_context_signer_in_struct() {
        let source = r#"
            use anchor_lang::prelude::*;

            #[derive(Accounts)]
            pub struct Resize<'info> {
                #[account(mut, has_one = authority)]
                pub data: Account<'info, DataAccount>,
                pub authority: Signer<'info>,
                #[account(mut)]
                pub payer: Signer<'info>,
                pub system_program: Program<'info, System>,
            }

            pub fn resize(ctx: Context<Resize>, new_size: usize) -> Result<()> {
                let info = ctx.accounts.data.to_account_info();
                let rent = Rent::get()?;
                let needed = rent.minimum_balance(new_size).saturating_sub(info.lamports());
                info.realloc(new_size, false)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Signer enforced by Signer<'info> in the Accounts struct should not be flagged"
        );
    }

    // idx 1: private helper whose signer + rent checks live in its only caller.
    #[test]
    fn test_no_finding_checks_in_caller() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            pub fn process_resize(accounts: &[AccountInfo], new_len: usize) -> ProgramResult {
                let authority = &accounts[0];
                let target = &accounts[1];
                if !authority.is_signer {
                    return Err(ProgramError::MissingRequiredSignature);
                }
                let rent = Rent::get()?;
                if target.lamports() < rent.minimum_balance(new_len) {
                    return Err(ProgramError::AccountNotRentExempt);
                }
                grow(target, new_len)
            }

            fn grow(account: &AccountInfo, new_len: usize) -> ProgramResult {
                account.realloc(new_len, false)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Helper whose checks live in the caller should not be flagged"
        );
    }

    // idx 2: signer verified via assert_signer() helper (Metaplex/SPL idiom).
    #[test]
    fn test_no_finding_assert_signer_helper() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            pub fn resize_metadata(account: &AccountInfo, payer: &AccountInfo, new_size: usize) -> ProgramResult {
                assert_signer(payer)?;
                let rent = Rent::get()?;
                let required = rent.minimum_balance(new_size);
                if account.lamports() < required {
                    return Err(ProgramError::AccountNotRentExempt);
                }
                account.realloc(new_size, false)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "assert_signer() helper should satisfy the signer check"
        );
    }

    // idx 3: non-#[test] helper function inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_helper_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;
                use solana_program::account_info::AccountInfo;

                fn make_resized_fixture(account: &AccountInfo) {
                    account.realloc(256, false).unwrap();
                }

                #[test]
                fn resizes_correctly() {
                    let _ = make_resized_fixture;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Helpers inside a #[cfg(test)] module should not be flagged"
        );
    }

    // idx 4: .realloc() on a non-account, single-argument buffer wrapper.
    #[test]
    fn test_no_finding_non_account_buffer_realloc() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            struct ScratchBuffer { data: Vec<u8> }

            fn grow_scratch(buf: &mut ScratchBuffer, new_len: usize) {
                buf.realloc(new_len);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Single-arg realloc on a non-account buffer should not be flagged"
        );
    }
}
