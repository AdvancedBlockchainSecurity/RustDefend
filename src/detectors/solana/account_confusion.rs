use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct AccountConfusionDetector;

impl Detector for AccountConfusionDetector {
    fn id(&self) -> &'static str {
        "SOL-004"
    }
    fn name(&self) -> &'static str {
        "account-confusion"
    }
    fn description(&self) -> &'static str {
        "Detects manual account deserialization without discriminator check"
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
        // Require Solana-specific source markers to avoid cross-chain FPs
        if !ctx.source.contains("solana_program")
            && !ctx.source.contains("anchor_lang")
            && !ctx.source.contains("AccountInfo")
            && !ctx.source.contains("ProgramResult")
            && !ctx.source.contains("solana_sdk")
        {
            return Vec::new();
        }

        // Skip framework/library source files and code generators
        let file_str = ctx.file_path.to_string_lossy();
        if file_str.contains("/anchor-spl/")
            || file_str.contains("/anchor_spl/")
            || file_str.contains("/anchor-lang/")
            || file_str.contains("/anchor_lang/")
            || file_str.contains("/codegen/")
            || file_str.contains("/interface/src/")
            || file_str.contains("/spl-token/")
            || file_str.contains("/spl_token/")
        {
            return Vec::new();
        }

        // Build a map of every locally-defined function's body source so that a
        // discriminator check factored out into a helper can be resolved.
        let mut fn_collector = FunctionCollector {
            functions: Vec::new(),
        };
        fn_collector.visit_file(&ctx.ast);
        let mut local_fn_bodies: HashMap<String, String> = HashMap::new();
        for f in &fn_collector.functions {
            local_fn_bodies
                .entry(f.sig.ident.to_string())
                .or_insert_with(|| fn_body_source(f));
        }

        let mut findings = Vec::new();
        let mut visitor = ConfusionVisitor {
            findings: &mut findings,
            ctx,
            local_fn_bodies: &local_fn_bodies,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct ConfusionVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    local_fn_bodies: &'a HashMap<String, String>,
}

impl<'ast, 'a> Visit<'ast> for ConfusionVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Do not descend into `#[cfg(test)]` modules: their functions are
        // compiled only for test builds, operate on test-authored bytes, and
        // never ship in the program binary, so account-type confusion of
        // attacker-controlled data is not reachable there.
        if is_cfg_test(&module.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test/pack/unpack/deserialization utility functions
        if fn_name.contains("test")
            || fn_name.starts_with("pack")
            || fn_name.starts_with("unpack")
            || fn_name.contains("_pack")
            || fn_name.contains("_unpack")
            || fn_name.contains("deserialize")
            || fn_name.contains("serialize")
            || fn_name.starts_with("gen_")
            || fn_name.starts_with("generate_")
            || has_attribute(&func.attrs, "test")
            || is_cfg_test(&func.attrs)
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

        // Check for manual deserialization. Match only genuine call/path token
        // forms (`::name (` / `. name (`) rather than bare substrings, so the
        // word "deserialize"/"unpack" appearing inside a string literal (e.g. a
        // `msg!("failed to deserialize ...")` log) does not trigger a finding.
        // A real deserialization site is always a qualified or method call, so
        // no true positive is lost.
        let has_deser = body_src.contains(":: try_from_slice")
            || body_src.contains(". try_from_slice")
            || body_src.contains(":: try_deserialize")
            || body_src.contains(". try_deserialize")
            || body_src.contains(":: deserialize")
            || body_src.contains(". deserialize")
            || body_src.contains(":: unpack")
            || body_src.contains(". unpack");

        if !has_deser {
            return;
        }

        let has_unpack_call = body_src.contains(":: unpack") || body_src.contains(". unpack");

        // spl_token's `Pack::unpack` (and spl-token-2022's `StateWithExtensions`)
        // internally enforce the exact packed length and reject uninitialized
        // accounts via `IsInitialized`, so account-type confusion is impossible.
        // Only the `unpack_unchecked` / `unpack_from_slice` variants skip those
        // checks and remain flagged; likewise a raw `T::try_from_slice` alongside
        // the unpack keeps the finding.
        let spl_checked_unpack = (body_src.contains("spl_token")
            || body_src.contains("StateWithExtensions"))
            && has_unpack_call
            && !body_src.contains("unpack_unchecked")
            && !body_src.contains("unpack_from_slice")
            && !body_src.contains(":: try_from_slice")
            && !body_src.contains(". try_from_slice");

        // Anchor's derived `AccountDeserialize::try_deserialize` validates the
        // 8-byte discriminator before touching any field. The unsafe variant is
        // `try_deserialize_unchecked`, which stays flagged.
        let anchor_checked_deser = (body_src.contains(":: try_deserialize")
            || body_src.contains(". try_deserialize"))
            && !body_src.contains("try_deserialize_unchecked");

        // A discriminator/tag check may be factored into a helper. Resolve the
        // bodies of locally-called functions and treat this function as safe if
        // any of them performs the check (the `?`/early-return propagates the
        // failure before deserialization).
        let mut helper_checks_discriminator = false;
        for name in collect_call_names(func) {
            if name == fn_name {
                continue;
            }
            if let Some(helper_body) = self.local_fn_bodies.get(&name) {
                if body_has_discriminator_check(helper_body) {
                    helper_checks_discriminator = true;
                    break;
                }
            }
        }

        // Check for discriminator check (first 8 bytes)
        let has_discriminator = body_has_discriminator_check(&body_src)
            || fn_src.contains("IsInitialized")
            || spl_checked_unpack
            || anchor_checked_deser
            || helper_checks_discriminator;

        if !has_discriminator {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "SOL-004".to_string(),
                name: "account-confusion".to_string(),
                severity: Severity::High,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' deserializes account data without discriminator validation",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Check the first 8 bytes of account data as a discriminator before deserialization, or use Anchor's `Account<'info, T>`".to_string(),
                chain: Chain::Solana,
            });
        }
    }
}

/// Returns true if the given function-body token source contains a recognizable
/// first-8-bytes discriminator / type-tag check. Accepts the several token-stream
/// spellings of a `data[..8]` read (`[.. 8]`, `[0 .. 8]`, `.get (.. 8)`), as well
/// as the common named-check conventions (`DISCRIMINATOR`, `is_initialized`, ...).
fn body_has_discriminator_check(body_src: &str) -> bool {
    body_src.contains("discriminator")
        || body_src.contains("DISCRIMINATOR")
        || body_src.contains("[.. 8]")
        || body_src.contains("[..8]")
        || body_src.contains("[0 .. 8]")
        || body_src.contains("[0..8]")
        || body_src.contains(". get (.. 8)")
        || body_src.contains(".get(..8)")
        || body_src.contains("account_type")
        || body_src.contains("is_initialized")
        || body_src.contains("IsInitialized")
        || body_src.contains("assert_initialized")
}

/// Returns true if any attribute is a `#[cfg(test)]` gate.
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if attr.path().is_ident("cfg") {
            let toks = attr.meta.to_token_stream().to_string();
            // `#[cfg(test)]` renders as `cfg (test)`. Avoid matching
            // `cfg(feature = "test-...")`, which is a real (shipped) config.
            return toks.contains("test") && !toks.contains("feature");
        }
        false
    })
}

/// Collect the names of functions/methods directly called within `func`.
fn collect_call_names(func: &ItemFn) -> Vec<String> {
    struct Collector {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for Collector {
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
    let mut collector = Collector { names: Vec::new() };
    collector.visit_item_fn(func);
    collector.names
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
        AccountConfusionDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_discriminator() {
        let source = r#"
            fn load_account(account: &AccountInfo) {
                let data = MyState::try_from_slice(&account.data.borrow()).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing discriminator");
    }

    #[test]
    fn test_no_finding_with_discriminator() {
        let source = r#"
            fn load_account(account: &AccountInfo) {
                let data = account.data.borrow();
                if data[..8] != MyState::DISCRIMINATOR {
                    return Err(ProgramError::InvalidAccountData);
                }
                let state = MyState::try_from_slice(&data[8..]).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with discriminator check"
        );
    }

    // --- FP idx 0: spl_token Pack::unpack is self-validating ---
    #[test]
    fn test_no_finding_spl_token_unpack() {
        let source = r#"
            fn token_balance(token_account: &AccountInfo) -> Result<u64, ProgramError> {
                let acc = spl_token::state::Account::unpack(&token_account.data.borrow())?;
                Ok(acc.amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "spl_token Pack::unpack is length/IsInitialized-checked and must not flag"
        );
    }

    #[test]
    fn test_flags_spl_unpack_unchecked() {
        // The unchecked variant skips the IsInitialized/length validation and
        // must still be flagged.
        let source = r#"
            fn token_balance(token_account: &AccountInfo) -> Result<u64, ProgramError> {
                let acc = spl_token::state::Account::unpack_unchecked(&token_account.data.borrow())?;
                Ok(acc.amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "unpack_unchecked skips validation and should be flagged"
        );
    }

    // --- FP idx 1: Anchor try_deserialize validates the discriminator ---
    #[test]
    fn test_no_finding_anchor_try_deserialize() {
        let source = r#"
            fn load_pool(info: &AccountInfo) -> Result<Pool> {
                let mut data: &[u8] = &info.data.borrow();
                Pool::try_deserialize(&mut data)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Anchor try_deserialize checks the discriminator and must not flag"
        );
    }

    #[test]
    fn test_flags_anchor_try_deserialize_unchecked() {
        let source = r#"
            fn load_pool(info: &AccountInfo) -> Result<Pool> {
                let mut data: &[u8] = &info.data.borrow();
                Pool::try_deserialize_unchecked(&mut data)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "try_deserialize_unchecked skips the discriminator check and should be flagged"
        );
    }

    // --- FP idx 2: discriminator check extracted into a local helper ---
    #[test]
    fn test_no_finding_discriminator_in_helper() {
        let source = r#"
            fn verify_pool_header(data: &[u8]) -> Result<(), ProgramError> {
                if data[..8] != Pool::DISCRIMINATOR {
                    return Err(ProgramError::InvalidAccountData);
                }
                Ok(())
            }

            fn load_pool(info: &AccountInfo) -> Result<Pool, ProgramError> {
                let data = info.data.borrow();
                verify_pool_header(&data)?;
                Pool::try_from_slice(&data[8..]).map_err(|_| ProgramError::InvalidAccountData)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Discriminator check factored into a resolved local helper must not flag"
        );
    }

    #[test]
    fn test_flags_when_helper_has_no_check() {
        // A helper that does NOT check the discriminator must not suppress.
        let source = r#"
            fn log_something(data: &[u8]) {
                let _ = data.len();
            }

            fn load_pool(info: &AccountInfo) -> Result<Pool, ProgramError> {
                let data = info.data.borrow();
                log_something(&data);
                Pool::try_from_slice(&data).map_err(|_| ProgramError::InvalidAccountData)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A non-checking helper must not suppress the finding"
        );
    }

    // --- FP idx 3: slice-spelling variants of the 8-byte check ---
    #[test]
    fn test_no_finding_slice_spelling_tag() {
        let source = r#"
            const POOL_TAG: [u8; 8] = *b"pool\0\0\0\0";

            fn load_pool(info: &AccountInfo) -> Result<Pool, ProgramError> {
                let data = info.data.borrow();
                if data[0..8] != POOL_TAG {
                    return Err(ProgramError::InvalidAccountData);
                }
                Pool::try_from_slice(&data[8..]).map_err(|_| ProgramError::InvalidAccountData)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A data[0..8] tag comparison is a valid discriminator check and must not flag"
        );
    }

    // --- FP idx 4: non-#[test] helper inside a #[cfg(test)] module ---
    #[test]
    fn test_no_finding_helper_in_cfg_test_module() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            #[cfg(test)]
            mod tests {
                use super::*;

                fn fixture_state(bytes: &[u8]) -> MyState {
                    MyState::try_from_slice(bytes).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A helper inside a #[cfg(test)] module must not flag"
        );
    }

    // --- FP idx 5: 'deserialize' inside a string literal ---
    #[test]
    fn test_no_finding_deserialize_in_string_literal() {
        let source = r#"
            use solana_program::pubkey::Pubkey;

            fn warn_bad_account(key: &Pubkey) {
                msg!("failed to deserialize account {}", key);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "'deserialize' inside a log string is not a deserialization site"
        );
    }
}
