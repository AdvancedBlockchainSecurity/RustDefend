use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{FnArg, ItemFn, ItemMod, Pat};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;
use crate::utils::call_graph::build_call_graph;

pub struct UnvalidatedSysvarDetector;

impl Detector for UnvalidatedSysvarDetector {
    fn id(&self) -> &'static str {
        "SOL-021"
    }
    fn name(&self) -> &'static str {
        "unvalidated-sysvar"
    }
    fn description(&self) -> &'static str {
        "Detects sysvar parameters typed as AccountInfo without proper validation"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
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

        // Resolve local helper bodies + a call graph so that validation which is
        // factored out into a project-local `assert_*/validate_*` helper (FP idx 4)
        // can be recognized soundly by inspecting the helper's actual body, rather
        // than by a blanket name-based skip.
        let helper_bodies = collect_local_fn_bodies(&ctx.ast);
        let call_graph = build_call_graph(&ctx.ast);

        let mut findings = Vec::new();
        let mut visitor = SysvarVisitor {
            findings: &mut findings,
            ctx,
            helper_bodies: &helper_bodies,
            call_graph: &call_graph,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const SYSVAR_NAMES: &[&str] = &[
    "clock",
    "rent",
    "epoch_schedule",
    "slot_hashes",
    "slot_history",
    "stake_history",
    "recent_blockhashes",
    "instructions",
];

/// Match a sysvar name against whole underscore-delimited segments of an
/// identifier, rather than as a raw substring. This preserves true positives
/// (`clock_info`, `rent_account`, `instructions_sysvar`, `slot_hashes_info`)
/// while rejecting incidental substrings like `parent_account` /
/// `current_authority` / `different` that merely contain "rent" (FP idx 0).
fn ident_matches_sysvar(ident: &str) -> bool {
    let lower = ident.to_lowercase();
    SYSVAR_NAMES.iter().any(|name| {
        lower == *name
            || lower.starts_with(&format!("{}_", name))
            || lower.ends_with(&format!("_{}", name))
            || lower.contains(&format!("_{}_", name))
    })
}

/// Extract the bound identifier of a typed function parameter, if it is a
/// simple `name: Type` binding (the only form real sysvar params take).
fn param_ident(arg: &FnArg) -> Option<String> {
    if let FnArg::Typed(pt) = arg {
        if let Pat::Ident(pi) = &*pt.pat {
            return Some(pi.ident.to_string());
        }
    }
    None
}

/// Type-token string of a typed parameter (excludes the binding name).
fn param_type_str(arg: &FnArg) -> Option<String> {
    if let FnArg::Typed(pt) = arg {
        return Some(pt.ty.to_token_stream().to_string());
    }
    None
}

/// Does this (token-stream-rendered) function body contain a recognized sysvar
/// validation? Token-stream rendering inserts spaces around `::`, so both the
/// spaced and unspaced spellings are matched.
fn body_has_sysvar_validation(body: &str) -> bool {
    body.contains("from_account_info")
        || body.contains("Sysvar :: get")
        || body.contains("Sysvar::get")
        || body.contains("sysvar::")
        // FP idx 1: the lowercase `sysvar::` path renders as `sysvar ::` in the
        // token stream, so the original allow-list entry never matched. This is
        // the hand-written address-pinning pattern (`clock_info.key != &sysvar::clock::id()`).
        || body.contains("sysvar ::")
        // FP idx 1 / idx 4: explicit key pinning via `sysvar::*::check_id(info.key)`.
        || body.contains("check_id")
        || body.contains("Clock :: get")
        || body.contains("Clock::get")
        || body.contains("Rent :: get")
        || body.contains("Rent::get")
        || body.contains("EpochSchedule :: get")
        || body.contains("EpochSchedule::get")
        // FP idx 2: the instructions sysvar cannot be read via Sysvar::get()/
        // from_account_info(); these self-validating APIs internally call
        // check_id on the passed account and are the officially recommended way
        // to introspect it.
        || body.contains("load_instruction_at_checked")
        || body.contains("get_instruction_relative")
        || body.contains("load_current_index_checked")
        // FP idx 1: hand-written comparison of the account key against a fixed
        // sysvar address constant.
        || (body.contains(". key") && (body.contains(":: id ()") || body.contains(":: ID")))
}

/// Does the body actually consume the sysvar account's contents (deserialize /
/// read raw bytes)? A pure pass-through wrapper that only forwards the
/// `AccountInfo` handle into a CPI (FP idx 3) never trusts the account's data
/// and therefore cannot be exploited by substituting a fake sysvar.
fn body_consumes_account_data(body: &str) -> bool {
    body.contains("try_borrow_data")
        || body.contains("try_borrow_mut_data")
        || body.contains("deserialize")
        || body.contains("from_le_bytes")
        || body.contains("from_be_bytes")
        || body.contains(". data")
}

/// Collect top-level `fn` bodies (token-stream strings) keyed by name so that a
/// caller's local helper can be resolved back to its body.
fn collect_local_fn_bodies(ast: &syn::File) -> HashMap<String, String> {
    let mut map = HashMap::new();
    for item in &ast.items {
        if let syn::Item::Fn(func) = item {
            map.insert(
                func.sig.ident.to_string(),
                func.block.to_token_stream().to_string(),
            );
        }
    }
    map
}

struct SysvarVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    helper_bodies: &'a HashMap<String, String>,
    call_graph: &'a crate::utils::call_graph::CallGraph,
}

impl<'a> SysvarVisitor<'a> {
    /// Returns true if any local helper invoked by `fn_name` validates the
    /// sysvar in its own body (resolved via the call graph — no name-based
    /// guessing). This suppresses FP idx 4 without introducing false negatives:
    /// the helper must actually contain a validation token.
    fn helper_validates(&self, fn_name: &str) -> bool {
        if let Some(info) = self.call_graph.get(fn_name) {
            for callee in &info.calls {
                if let Some(body) = self.helper_bodies.get(callee) {
                    if body_has_sysvar_validation(body) {
                        return true;
                    }
                }
            }
        }
        false
    }
}

impl<'ast, 'a> Visit<'ast> for SysvarVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Skip `#[cfg(test)]` modules — their code encodes fixtures, not
        // shippable program logic.
        if has_attribute_with_value(&node.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        if fn_name.contains("test")
            || has_attribute(&func.attrs, "test")
            || has_attribute_with_value(&func.attrs, "cfg", "test")
        {
            return;
        }

        let fn_src = func.to_token_stream().to_string();

        // Skip if using Anchor's Sysvar<'info, T> type
        if fn_src.contains("Sysvar <") || fn_src.contains("Sysvar<") {
            return;
        }

        // Check if any parameter is a sysvar name typed as AccountInfo
        for param in &func.sig.inputs {
            // Must be typed as AccountInfo (check the type, not the whole arg,
            // so the binding name cannot spuriously match).
            let ty_str = match param_type_str(param) {
                Some(t) if t.contains("AccountInfo") => t,
                _ => continue,
            };
            let _ = ty_str;

            // Extract the binding identifier and match sysvar names against its
            // underscore-delimited segments (FP idx 0).
            let ident = match param_ident(param) {
                Some(i) => i,
                None => continue,
            };
            if !ident_matches_sysvar(&ident) {
                continue;
            }

            let body_src = fn_body_source(func);

            // Check for proper sysvar validation in this function's own body,
            // or delegated to a resolved local helper.
            if body_has_sysvar_validation(&body_src) || self.helper_validates(&fn_name) {
                continue;
            }

            // Only flag when the body actually reads/trusts the sysvar's data.
            // Pure pass-through wrappers (forward the handle into a CPI) are not
            // vulnerable (FP idx 3).
            if !body_consumes_account_data(&body_src) {
                continue;
            }

            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "SOL-021".to_string(),
                name: "unvalidated-sysvar".to_string(),
                severity: Severity::Medium,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' accepts sysvar as AccountInfo without from_account_info() or Sysvar::get() validation",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Use Sysvar::get() or from_account_info() to validate sysvar accounts, or use Anchor's Sysvar<'info, T> type".to_string(),
                chain: Chain::Solana,
            });
            break; // One finding per function
        }
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
        UnvalidatedSysvarDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unvalidated_clock_sysvar() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn process(accounts: &[AccountInfo], clock_info: &AccountInfo) {
                let data = clock_info.try_borrow_data().unwrap();
                let timestamp = u64::from_le_bytes(data[32..40].try_into().unwrap());
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect unvalidated clock sysvar"
        );
    }

    #[test]
    fn test_detects_unvalidated_rent_sysvar() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn process(rent_account: &AccountInfo) {
                let data = rent_account.try_borrow_data().unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect unvalidated rent sysvar"
        );
    }

    #[test]
    fn test_no_finding_with_from_account_info() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn process(clock_info: &AccountInfo) {
                let clock = Clock::from_account_info(clock_info)?;
                let timestamp = clock.unix_timestamp;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with from_account_info validation"
        );
    }

    #[test]
    fn test_no_finding_with_sysvar_get() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn process(clock_info: &AccountInfo) {
                let clock = Clock::get()?;
                let timestamp = clock.unix_timestamp;
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with Sysvar::get()");
    }

    #[test]
    fn test_skips_anchor_sysvar_type() {
        let source = r#"
            use anchor_lang::prelude::*;
            fn process(clock: Sysvar<'info, Clock>) {
                let timestamp = clock.unix_timestamp;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should skip Anchor Sysvar<'info, T> type"
        );
    }

    #[test]
    fn test_no_finding_non_sysvar_account() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn process(user_account: &AccountInfo) {
                let data = user_account.try_borrow_data().unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag non-sysvar AccountInfo params"
        );
    }

    // FP idx 0: "rent" is a substring of common identifiers like `parent_account`
    // and `current_authority`, but neither is a sysvar.
    #[test]
    fn test_no_finding_rent_substring_in_param_names() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;

            fn update_child(parent_account: &AccountInfo, current_authority: &AccountInfo) -> ProgramResult {
                if !current_authority.is_signer {
                    return Err(solana_program::program_error::ProgramError::MissingRequiredSignature);
                }
                let data = parent_account.try_borrow_data()?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag non-sysvar params whose names merely contain 'rent'"
        );
    }

    // FP idx 1: explicit key pinning against the canonical sysvar address.
    #[test]
    fn test_no_finding_manual_sysvar_key_check() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::program_error::ProgramError;

            fn process(clock_info: &AccountInfo) -> ProgramResult {
                if clock_info.key != &solana_program::sysvar::clock::id() {
                    return Err(ProgramError::InvalidArgument);
                }
                let data = clock_info.try_borrow_data()?;
                let timestamp = i64::from_le_bytes(data[32..40].try_into().unwrap());
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the account key is pinned to the sysvar address"
        );
    }

    // FP idx 2: instructions sysvar consumed via a self-validating helper.
    #[test]
    fn test_no_finding_instructions_load_checked() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::sysvar::instructions::load_instruction_at_checked;

            fn verify_signature(instructions_sysvar: &AccountInfo) -> ProgramResult {
                let ix = load_instruction_at_checked(0, instructions_sysvar)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag instructions sysvar used via load_instruction_at_checked"
        );
    }

    // FP idx 3: rent account forwarded into a CPI, never deserialized.
    #[test]
    fn test_no_finding_rent_passthrough_cpi() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::program::invoke;

            fn create_token_account<'a>(
                account: &AccountInfo<'a>,
                mint: &AccountInfo<'a>,
                owner: &AccountInfo<'a>,
                rent_info: &AccountInfo<'a>,
                token_program: &AccountInfo<'a>,
            ) -> ProgramResult {
                let ix = spl_token::instruction::initialize_account(
                    token_program.key, account.key, mint.key, owner.key,
                )?;
                invoke(&ix, &[account.clone(), mint.clone(), owner.clone(), rent_info.clone(), token_program.clone()])
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a rent account that is only forwarded into a CPI"
        );
    }

    // FP idx 4: validation factored into a resolvable local helper.
    #[test]
    fn test_no_finding_validation_via_helper() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::program_error::ProgramError;

            fn assert_clock_sysvar(info: &AccountInfo) -> ProgramResult {
                if !solana_program::sysvar::clock::check_id(info.key) {
                    return Err(ProgramError::InvalidArgument);
                }
                Ok(())
            }

            fn read_timestamp(clock_info: &AccountInfo) -> ProgramResult {
                assert_clock_sysvar(clock_info)?;
                let data = clock_info.try_borrow_data()?;
                let _ts = i64::from_le_bytes(data[32..40].try_into().unwrap());
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when validation is delegated to a resolved local helper"
        );
    }

    // Sanity: a genuinely vulnerable helper-style program (no validation
    // anywhere) must still fire.
    #[test]
    fn test_still_flags_unvalidated_with_unrelated_helper() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;

            fn log_something(info: &AccountInfo) -> ProgramResult {
                Ok(())
            }

            fn read_timestamp(clock_info: &AccountInfo) -> ProgramResult {
                log_something(clock_info)?;
                let data = clock_info.try_borrow_data()?;
                let _ts = i64::from_le_bytes(data[32..40].try_into().unwrap());
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag when the called helper performs no sysvar validation"
        );
    }
}
