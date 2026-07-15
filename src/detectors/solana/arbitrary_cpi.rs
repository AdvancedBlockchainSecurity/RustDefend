use quote::ToTokens;
use syn::visit::Visit;
use syn::ItemFn;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;
use crate::utils::call_graph::{build_call_graph, CallGraph};

pub struct ArbitraryCpiDetector;

impl Detector for ArbitraryCpiDetector {
    fn id(&self) -> &'static str {
        "SOL-006"
    }
    fn name(&self) -> &'static str {
        "arbitrary-cpi"
    }
    fn description(&self) -> &'static str {
        "Detects CPI calls where the program target comes from untrusted input"
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
        // Require Solana-specific source markers to avoid cross-chain FPs
        if !ctx.source.contains("solana_program")
            && !ctx.source.contains("anchor_lang")
            && !ctx.source.contains("AccountInfo")
            && !ctx.source.contains("ProgramResult")
            && !ctx.source.contains("solana_sdk")
        {
            return Vec::new();
        }

        // Skip framework/library source files — these implement typed CPI
        // wrappers that ARE the validation layer
        let file_str = ctx.file_path.to_string_lossy();
        if file_str.contains("/anchor-spl/")
            || file_str.contains("/anchor_spl/")
            || file_str.contains("/anchor/spl/")
            || file_str.contains("/anchor-lang/")
            || file_str.contains("/anchor_lang/")
            || file_str.contains("/anchor/lang/")
            || file_str.contains("/spl-token/")
            || file_str.contains("/spl_token/")
            || file_str.contains("/codegen/")
            || file_str.contains("/interface/src/")
        {
            return Vec::new();
        }

        // Build a per-file call graph so we can resolve whether a called helper
        // actually performs the program-id check (rather than blindly trusting a
        // name). Built from the AST directly so it is independent of whatever the
        // scanner pipeline populated on the context.
        let call_graph = build_call_graph(&ctx.ast);

        let mut findings = Vec::new();
        let mut visitor = CpiVisitor {
            findings: &mut findings,
            ctx,
            call_graph,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct CpiVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    call_graph: CallGraph,
}

impl<'ast, 'a> Visit<'ast> for CpiVisitor<'a> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_src = func.to_token_stream().to_string();

        // Skip if using Anchor's Program<'info, T> type (auto-validates)
        if fn_src.contains("Program <") || fn_src.contains("Program<") {
            return;
        }

        let body_src = fn_body_source(func);

        // Look for CPI invocation patterns
        let has_cpi = body_src.contains("invoke (")
            || body_src.contains("invoke(")
            || body_src.contains("invoke_signed")
            || body_src.contains("CpiContext :: new")
            || body_src.contains("CpiContext::new");

        if !has_cpi {
            return;
        }

        let fn_name = func.sig.ident.to_string();

        // Skip helper/wrapper functions that pass through CPI
        // These are utility functions like spl_token_transfer, create_account, etc.
        // The actual program ID is typically hardcoded inside
        if fn_name.starts_with("spl_")
            || fn_name.starts_with("create_")
            || fn_name.starts_with("close_")
            || fn_name.starts_with("initialize_")
            || fn_name.starts_with("transfer_")
            || fn_name.starts_with("mint_")
            || fn_name.starts_with("burn_")
            || fn_name.starts_with("approve_")
            || fn_name.starts_with("revoke_")
            || fn_name.starts_with("freeze_")
            || fn_name.starts_with("thaw_")
            || fn_name.starts_with("sync_")
            || fn_name.contains("_invoke")
            || fn_name.contains("_cpi")
        {
            return;
        }

        // Consider the function safe if it verifies the target program itself, OR
        // if it delegates that verification to a helper whose body we can resolve
        // and confirm performs the check.
        if !has_program_check(&body_src) && !self.helper_validates_program(&fn_name) {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "SOL-006".to_string(),
                name: "arbitrary-cpi".to_string(),
                severity: Severity::Critical,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' performs CPI without verifying the target program",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Validate the program account key against an expected program ID, or use Anchor's `Program<'info, T>` constraint".to_string(),
                chain: Chain::Solana,
            });
        }
    }
}

impl<'a> CpiVisitor<'a> {
    /// Returns true if `fn_name` calls a validation helper whose *resolved* body
    /// actually performs a program-id check. We only consider callees whose name
    /// signals a validation role (check/validate/verify/assert/require/ensure) to
    /// keep the scope tight, but the decision is gated on the resolved body
    /// containing a real program check — never on the name alone. Unresolvable
    /// callees are treated as "no check", which keeps detection intact.
    fn helper_validates_program(&self, fn_name: &str) -> bool {
        let calls = match self.call_graph.get(fn_name) {
            Some(info) => &info.calls,
            None => return false,
        };
        for callee in calls {
            let lc = callee.to_lowercase();
            let looks_like_check = lc.contains("check")
                || lc.contains("validate")
                || lc.contains("verify")
                || lc.contains("assert")
                || lc.contains("require")
                || lc.contains("ensure");
            if !looks_like_check {
                continue;
            }
            if let Some(body) = resolve_fn_body(&self.ctx.ast, callee) {
                if has_program_check(&body) {
                    return true;
                }
            }
        }
        false
    }
}

/// Resolve a top-level function's body source by name from the file AST.
fn resolve_fn_body(ast: &syn::File, name: &str) -> Option<String> {
    for item in &ast.items {
        if let syn::Item::Fn(func) = item {
            if func.sig.ident == name {
                return Some(fn_body_source(func));
            }
        }
    }
    None
}

/// Returns true if the function body contains evidence that the CPI target
/// program is pinned to a known/expected program id.
fn has_program_check(body_src: &str) -> bool {
    // Equality / inequality comparisons against a known program id, including the
    // raw `AccountInfo.key` field form (`program . key != & EXPECTED`). Returning
    // `IncorrectProgramId` is itself strong evidence of a program-id guard.
    let has_comparison = body_src.contains("program_id ==")
        || body_src.contains("== program_id")
        || body_src.contains("program_id !=")
        || body_src.contains("!= program_id")
        || body_src.contains("key () ==")
        || body_src.contains("key() ==")
        || body_src.contains("key () !=")
        || body_src.contains("key() !=")
        || body_src.contains(". key ==")
        || body_src.contains(". key !=")
        || body_src.contains("IncorrectProgramId");

    // Hardcoded / well-known program references.
    let has_hardcoded = body_src.contains("system_program ::")
        || body_src.contains("system_program")
        || body_src.contains("token :: ID")
        || body_src.contains("token :: id")
        || body_src.contains("spl_token :: id")
        || body_src.contains("spl_token :: ID")
        || body_src.contains("token_program")
        || body_src.contains("Program <")
        || body_src.contains("system_instruction")
        || body_src.contains("spl_token")
        || body_src.contains("spl_associated")
        || body_src.contains("rent ::")
        || body_src.contains("Rent ::");

    // Macro-based key assertions: Anchor's `require_keys_eq!` / `require_eq!` and
    // native `assert_eq!`. Only counted when the same body also references a key
    // or program_id, so unrelated `assert_eq!` calls are not mistaken for checks.
    let has_macro_check = (body_src.contains(". key") || body_src.contains("program_id"))
        && (body_src.contains("require_keys_eq !")
            || body_src.contains("require_keys_neq !")
            || body_src.contains("require_eq !")
            || body_src.contains("require_neq !")
            || body_src.contains("assert_eq !")
            || body_src.contains("assert_ne !"));

    has_comparison || has_hardcoded || has_macro_check || has_hardcoded_program_id_init(body_src)
}

/// Detects an `Instruction { program_id: <compile-time constant>, .. }` init,
/// where the CPI target is baked in at compile time and therefore not
/// attacker-controlled. A target initialized from a parameter or `*account.key`
/// (the actual vulnerability) is NOT matched.
fn has_hardcoded_program_id_init(body_src: &str) -> bool {
    let needle = "program_id :";
    let mut start = 0;
    while let Some(rel) = body_src[start..].find(needle) {
        let val_start = start + rel + needle.len();
        let rest = &body_src[val_start..];
        // The value expression runs up to the next top-level delimiter.
        let end = rest.find([',', ';', '}']).unwrap_or(rest.len());
        let value = rest[..end].trim();
        if value_is_const_program_id(value) {
            return true;
        }
        start = val_start;
    }
    false
}

/// Returns true if a `program_id:` initializer value is a compile-time constant
/// program id: an associated `:: ID` const / `:: id()` fn, or a
/// SCREAMING_SNAKE_CASE constant (possibly the last segment of a path).
fn value_is_const_program_id(value: &str) -> bool {
    if value.is_empty() {
        return false;
    }
    // Path to an associated `ID` const or `id()` fn, e.g. `whirlpool :: ID`,
    // `spl_token :: id ()`, `crate :: ID`.
    if value.contains(":: ID") || value.contains(":: id") {
        return true;
    }
    // A SCREAMING_SNAKE_CASE constant, possibly the last path segment
    // (`constants :: ORACLE_PROGRAM_ID`). A `*account.key` / lowercase-parameter
    // target ends in a non-constant identifier and is left flagged.
    let last_ident = value
        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .filter(|s| !s.is_empty())
        .last();
    matches!(last_ident, Some(id) if is_screaming_snake(id))
}

/// True for identifiers like `ORACLE_PROGRAM_ID` / `DEX_ID` — all uppercase
/// letters, digits and underscores, with at least one letter.
fn is_screaming_snake(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        && s.chars().any(|c| c.is_ascii_uppercase())
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
        ArbitraryCpiDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_arbitrary_cpi() {
        let source = r#"
            fn do_transfer(program: &AccountInfo, from: &AccountInfo, to: &AccountInfo) {
                invoke(
                    &transfer_ix,
                    &[from.clone(), to.clone(), program.clone()],
                )?;
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect arbitrary CPI target");
    }

    #[test]
    fn test_no_finding_with_program_check() {
        let source = r#"
            fn do_transfer(program: &AccountInfo, from: &AccountInfo, to: &AccountInfo) {
                if program.key() == &spl_token::id() {
                    invoke(
                        &transfer_ix,
                        &[from.clone(), to.clone(), program.clone()],
                    )?;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with program ID check");
    }

    // FP idx 1: program id verified with a `!=` early-return guard on the raw
    // `AccountInfo.key` field before the CPI.
    #[test]
    fn test_no_finding_with_not_equal_key_guard() {
        let source = r#"
            fn forward(program: &AccountInfo, accounts: &[AccountInfo], ix: &Instruction) -> ProgramResult {
                if program.key != &DEX_PROGRAM_ID {
                    return Err(ProgramError::IncorrectProgramId);
                }
                invoke(ix, accounts)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the program key is guarded with a != check"
        );
    }

    // FP idx 2: program id verified via the `require_keys_eq!` macro.
    #[test]
    fn test_no_finding_with_require_keys_eq_macro() {
        let source = r#"
            use anchor_lang::prelude::*;
            pub fn route(ctx: Context<Route>, data: Vec<u8>) -> Result<()> {
                require_keys_eq!(ctx.accounts.dex.key(), whirlpool::ID, ErrorCode::BadProgram);
                invoke(&build_ix(&data), &[ctx.accounts.dex.to_account_info()])?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when program id is asserted via require_keys_eq!"
        );
    }

    // FP idx 3: instruction built with a hardcoded compile-time program_id const.
    #[test]
    fn test_no_finding_with_hardcoded_program_id_const() {
        let source = r#"
            fn ping_oracle(accounts: &[AccountInfo]) -> ProgramResult {
                let ix = Instruction {
                    program_id: ORACLE_PROGRAM_ID,
                    accounts: vec![AccountMeta::new_readonly(*accounts[0].key, false)],
                    data: vec![1],
                };
                invoke(&ix, accounts)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the CPI target is a hardcoded program id constant"
        );
    }

    // FP idx 4: program validation delegated to a resolvable helper function.
    #[test]
    fn test_no_finding_with_validation_helper() {
        let source = r#"
            fn check_dex_program(info: &AccountInfo) -> ProgramResult {
                if info.key != &DEX_ID {
                    return Err(ProgramError::IncorrectProgramId);
                }
                Ok(())
            }

            fn execute_route(program: &AccountInfo, accounts: &[AccountInfo], ix: &Instruction) -> ProgramResult {
                check_dex_program(program)?;
                invoke(ix, accounts)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when program validation is delegated to a resolvable helper"
        );
    }

    // Guard soundness: a target initialized from untrusted input (not a const)
    // must still be flagged even though it uses `program_id:` struct-init syntax.
    #[test]
    fn test_still_flags_program_id_from_untrusted_input() {
        let source = r#"
            fn relay(accounts: &[AccountInfo], attacker_program: Pubkey) -> ProgramResult {
                let ix = Instruction {
                    program_id: attacker_program,
                    accounts: vec![AccountMeta::new_readonly(*accounts[0].key, false)],
                    data: vec![1],
                };
                invoke(&ix, accounts)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag when program id comes from untrusted input"
        );
    }
}
