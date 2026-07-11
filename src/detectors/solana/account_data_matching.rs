use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ExprCall, ExprMethodCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct AccountDataMatchingDetector;

impl Detector for AccountDataMatchingDetector {
    fn id(&self) -> &'static str {
        "SOL-017"
    }
    fn name(&self) -> &'static str {
        "account-data-matching"
    }
    fn description(&self) -> &'static str {
        "Detects account data deserialization without field validation"
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

        // Build a map of every function's tokenized body, so that when a caller
        // delegates its field validation to a helper (a very common native-Solana
        // pattern, e.g. `assert_vault_owner(account, &state)?`) we can RESOLVE that
        // helper's actual body and confirm it really performs a comparison/return-Err
        // before treating the caller as validated. Helpers that cannot be resolved
        // in this file are never assumed safe (no false negatives).
        let mut helper_bodies: HashMap<String, String> = HashMap::new();
        let mut fc = FunctionCollector {
            functions: Vec::new(),
        };
        fc.visit_file(&ctx.ast);
        for f in &fc.functions {
            helper_bodies
                .entry(f.sig.ident.to_string())
                .or_insert_with(|| fn_body_source(f));
        }

        let mut findings = Vec::new();
        let mut visitor = DataMatchingVisitor {
            findings: &mut findings,
            ctx,
            helper_bodies: &helper_bodies,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct DataMatchingVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    helper_bodies: &'a HashMap<String, String>,
}

impl<'ast, 'a> Visit<'ast> for DataMatchingVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Do not descend into `#[cfg(test)]` modules: fixture helpers there are
        // test-only, never ship on-chain, and are outside the threat model.
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip validation/verification/parsing utility functions and tests
        if fn_name.contains("validate")
            || fn_name.contains("verify")
            || fn_name.contains("check")
            || fn_name.contains("parse")
            || fn_name.contains("unpack")
            || fn_name.contains("test")
            || has_attribute(&func.attrs, "test")
        {
            return;
        }

        let fn_src = func.to_token_stream().to_string();

        // Skip Anchor Account<'info, T> patterns
        if fn_src.contains("Account <") || fn_src.contains("Account<") {
            if fn_src.contains("Context") {
                return;
            }
        }

        let body_src = fn_body_source(func);

        // Distinguish real account-data borrowing from a bare Borsh deserialize.
        let has_borrow = body_src.contains("try_borrow_data")
            || body_src.contains("data . borrow")
            || body_src.contains("data.borrow");
        let has_deserialize =
            body_src.contains("try_from_slice") || body_src.contains("deserialize");

        if !has_borrow && !has_deserialize {
            return;
        }

        // A deserialize with NO account-data borrow that operates on a raw byte
        // slice parameter (e.g. `MyInstruction::try_from_slice(instruction_data)`
        // in a native entrypoint) is parsing INSTRUCTION data, not account data.
        // "Account data matching" is inapplicable — there are no deserialized
        // account fields to validate against expected keys.
        if !has_borrow && has_deserialize {
            let params = byte_slice_param_names(func);
            if deserializes_byte_slice(&body_src, &params) {
                return;
            }
        }

        // Check for field validation after deserialization.
        // Note: tokenized source uses spaces around operators and macros
        // e.g., "assert_eq !" for "assert_eq!", "= =" for "==".
        let has_validation =
            body_has_inline_validation(&body_src) || self.has_delegated_validation(func);

        if !has_validation {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "SOL-017".to_string(),
                name: "account-data-matching".to_string(),
                severity: Severity::High,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' borrows/deserializes account data without field validation",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Validate deserialized account fields (e.g., assert_eq!, require!, discriminator check) before using the data, or use Anchor's Account<'info, T>".to_string(),
                chain: Chain::Solana,
            });
        }
    }
}

impl<'a> DataMatchingVisitor<'a> {
    /// Returns true when the function delegates its field validation to a
    /// helper it calls, AND that helper's resolved body actually contains a
    /// comparison / validation token. Only helpers whose name matches the
    /// validator naming heuristic and whose body we can resolve in-file are
    /// trusted — external/unresolvable helpers are never assumed safe.
    fn has_delegated_validation(&self, func: &ItemFn) -> bool {
        let mut collector = CalleeCollector { names: Vec::new() };
        collector.visit_block(&func.block);
        for name in &collector.names {
            if !is_validatorish_name(name) {
                continue;
            }
            if let Some(helper_body) = self.helper_bodies.get(name) {
                if body_has_inline_validation(helper_body) {
                    return true;
                }
            }
        }
        false
    }
}

/// Inline validation tokens recognized after a deserialization.
fn body_has_inline_validation(body_src: &str) -> bool {
    body_src.contains("assert_eq")
        || body_src.contains("assert_ne")
        || body_src.contains("= =")
        || body_src.contains("! =")
        || body_src.contains("==")
        || body_src.contains("!=")
        || body_src.contains("require")
        || body_src.contains("discriminator")
        || body_src.contains("DISCRIMINATOR")
        || body_src.contains("is_initialized")
        || body_src.contains("IsInitialized")
        // Anchor's `try_deserialize` verifies the 8-byte account discriminator
        // internally (exactly the validation SOL-017 enforces). Tokenized as
        // "try_deserialize (" — which does NOT match `try_deserialize_unchecked`,
        // so unchecked raw loads remain flagged.
        || body_src.contains("try_deserialize (")
        // A `match` on a deserialized tag/enum with an error arm is equivalent to
        // `if field != expected { return Err(..) }`, which the token list accepts.
        || (body_src.contains("match")
            && (body_src.contains("Err") || body_src.contains("err !")))
}

/// Heuristic: does this called-function name look like a validator/guard?
fn is_validatorish_name(name: &str) -> bool {
    let n = name.to_ascii_lowercase();
    n.contains("validate")
        || n.contains("verify")
        || n.contains("check")
        || n.contains("assert")
        || n.contains("ensure")
        || n.contains("require")
        || n.contains("guard")
}

/// Names of function parameters whose type is a byte slice (`&[u8]`), or which
/// are conventionally instruction-data payloads.
fn byte_slice_param_names(func: &ItemFn) -> Vec<String> {
    let mut names = Vec::new();
    for input in &func.sig.inputs {
        if let syn::FnArg::Typed(pat_type) = input {
            let ty = pat_type.ty.to_token_stream().to_string();
            let is_byte_slice = ty.contains("[u8]") || ty.contains("[ u8 ]");
            if let syn::Pat::Ident(pat_ident) = pat_type.pat.as_ref() {
                let name = pat_ident.ident.to_string();
                if is_byte_slice
                    || name == "instruction_data"
                    || name == "input"
                    || name == "ix_data"
                {
                    names.push(name);
                }
            }
        }
    }
    names
}

/// True when a deserialize call in `body_src` operates on one of the given
/// byte-slice parameters (i.e. it parses instruction/raw-slice data).
fn deserializes_byte_slice(body_src: &str, params: &[String]) -> bool {
    for p in params {
        let patterns = [
            format!("try_from_slice ({}", p),
            format!("try_from_slice (& {}", p),
            format!("try_from_slice (& mut {}", p),
            format!("deserialize ({}", p),
            format!("deserialize (& {}", p),
            format!("deserialize (& mut {}", p),
        ];
        if patterns.iter().any(|pat| body_src.contains(pat)) {
            return true;
        }
    }
    false
}

/// True if any attribute is `#[cfg(test)]` (or a cfg predicate mentioning test).
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path().is_ident("cfg") && {
            let tokens = attr.meta.to_token_stream().to_string();
            tokens.contains("test")
        }
    })
}

/// Collects the names of functions/methods called within a block.
struct CalleeCollector {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for CalleeCollector {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let syn::Expr::Path(expr_path) = node.func.as_ref() {
            if let Some(segment) = expr_path.path.segments.last() {
                self.names.push(segment.ident.to_string());
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
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
        AccountDataMatchingDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_field_validation() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn load_data(account: &AccountInfo) {
                let data = account.try_borrow_data().unwrap();
                let state = MyState::try_from_slice(&data).unwrap();
                process(state);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect missing field validation"
        );
    }

    #[test]
    fn test_no_finding_with_assert_eq() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn load_data(account: &AccountInfo) {
                let data = account.try_borrow_data().unwrap();
                let state = MyState::try_from_slice(&data).unwrap();
                assert_eq!(state.owner, expected_owner);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with assert_eq! validation"
        );
    }

    #[test]
    fn test_no_finding_with_require() {
        let source = r#"
            use anchor_lang::prelude::*;
            fn load_data(account: &AccountInfo) {
                let data = account.try_borrow_data().unwrap();
                let state = MyState::try_from_slice(&data).unwrap();
                require!(state.is_initialized, MyError::NotInitialized);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with require! validation"
        );
    }

    #[test]
    fn test_skips_anchor_context() {
        let source = r#"
            use anchor_lang::prelude::*;
            fn process(ctx: Context<MyAccounts>) {
                let account: Account<'_, MyState> = Account::try_from(&ctx.accounts.my_account).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should skip Anchor Account<> + Context patterns"
        );
    }

    #[test]
    fn test_skips_validate_functions() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            fn validate_account(account: &AccountInfo) {
                let data = account.try_borrow_data().unwrap();
                let state = MyState::try_from_slice(&data).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should skip validation functions");
    }

    // ---- False-positive regression tests (should NOT flag) ----

    #[test]
    fn test_no_finding_validation_delegated_to_helper() {
        // FP idx 0: the owner comparison lives in a resolvable helper; the `?`
        // propagates its Err. The caller must not be flagged.
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::program_error::ProgramError;

            fn load_vault(account: &AccountInfo) -> ProgramResult {
                let data = account.try_borrow_data()?;
                let state = Vault::try_from_slice(&data)?;
                assert_vault_owner(account, &state)?;
                process(&state);
                Ok(())
            }

            fn assert_vault_owner(account: &AccountInfo, state: &Vault) -> ProgramResult {
                if state.owner != *account.key {
                    return Err(ProgramError::InvalidAccountData);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when validation is delegated to a resolvable helper"
        );
    }

    #[test]
    fn test_no_finding_instruction_data_dispatch() {
        // FP idx 1: deserializing instruction_data (a &[u8] param) is not account data.
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::pubkey::Pubkey;

            fn process_instruction(
                program_id: &Pubkey,
                accounts: &[AccountInfo],
                instruction_data: &[u8],
            ) -> ProgramResult {
                let ix = MyInstruction::try_from_slice(instruction_data)?;
                match ix {
                    MyInstruction::Init => handle_init(program_id, accounts),
                    MyInstruction::Close => handle_close(program_id, accounts),
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag native entrypoint deserializing instruction data"
        );
    }

    #[test]
    fn test_no_finding_anchor_try_deserialize() {
        // FP idx 2: try_deserialize verifies the discriminator internally.
        let source = r#"
            use anchor_lang::prelude::*;

            fn read_vault(info: &AccountInfo) -> Result<Vault> {
                let mut data: &[u8] = &info.try_borrow_data()?;
                let vault = Vault::try_deserialize(&mut data)?;
                Ok(vault)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag Anchor try_deserialize (discriminator check)"
        );
    }

    #[test]
    fn test_still_flags_try_deserialize_unchecked() {
        // Ensure the try_deserialize allow does not leak to the unchecked variant.
        let source = r#"
            use anchor_lang::prelude::*;

            fn read_vault(info: &AccountInfo) -> Result<Vault> {
                let mut data: &[u8] = &info.try_borrow_data()?;
                let vault = Vault::try_deserialize_unchecked(&mut data)?;
                Ok(vault)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag try_deserialize_unchecked (no discriminator check)"
        );
    }

    #[test]
    fn test_no_finding_match_tag_with_error_arm() {
        // FP idx 3: match on a deserialized tag with an error fallback arm validates it.
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::program_error::ProgramError;

            fn load_pool(account: &AccountInfo) -> ProgramResult {
                let data = account.try_borrow_data()?;
                let state = PoolState::try_from_slice(&data)?;
                match state.account_type {
                    AccountType::Pool => process(&state),
                    _ => return Err(ProgramError::InvalidAccountData),
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag match-with-error-arm validation"
        );
    }

    #[test]
    fn test_no_finding_cfg_test_module_helper() {
        // FP idx 4: fixture helpers inside #[cfg(test)] modules must be skipped.
        let source = r#"
            #[cfg(test)]
            mod tests {
                use solana_program::account_info::AccountInfo;

                fn setup_state(account: &AccountInfo) -> MyState {
                    let data = account.try_borrow_data().unwrap();
                    MyState::try_from_slice(&data).unwrap()
                }

                #[test]
                fn works() {
                    let _ = 1;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag helpers inside #[cfg(test)] modules"
        );
    }
}
