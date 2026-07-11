use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ImplItemFn, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct RemainingAccountsDetector;

impl Detector for RemainingAccountsDetector {
    fn id(&self) -> &'static str {
        "SOL-013"
    }
    fn name(&self) -> &'static str {
        "unsafe-remaining-accounts"
    }
    fn description(&self) -> &'static str {
        "Detects ctx.remaining_accounts usage without owner/type/key validation"
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
        let mut findings = Vec::new();
        // Resolve every function body in this file (free fns + impl methods) so we
        // can inspect the bodies of validation helpers called from an instruction
        // handler (intra-file helper resolution for the delegation guard below).
        let fn_bodies = collect_fn_bodies(&ctx.ast);
        let mut visitor = RemainingAccountsVisitor {
            findings: &mut findings,
            ctx,
            fn_bodies,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Tokens that indicate the remaining accounts are being validated (owner /
/// type / key / discriminator checks). Note: `fn_body_source` renders the syn
/// token stream, so method calls/macros always carry a space before `(` / `!`
/// (e.g. `.key()` -> `key ()`, `require!` -> `require !`).
const SAFE_PATTERNS: &[&str] = &[
    "owner",
    "try_deserialize",
    "Account :: try_from",
    "AccountDeserialize",
    "discriminator",
    "DISCRIMINATOR",
    // Key equality checks — method-call form (`.key() == ...` / `.key() != ...`).
    // A key comparison in either polarity, followed by control flow, is a
    // validation; the negated form is exactly as strong as the `==` form.
    "key () ==",
    "key () !=",
    // Key equality checks — native `AccountInfo.key` field form (`.key == ...`).
    // In native Solana `AccountInfo.key` is a public `&Pubkey` field, not a method.
    "key ==",
    "key !=",
    // Anchor / vipers assertion macros. Each early-returns Err (or aborts the
    // transaction) on mismatch before any account data is read.
    "require_keys_eq",
    "require !",
    "require_eq",
    "assert_eq !",
    "assert_keys_eq",
    "assert_owner",
    "unwrap_key",
];

const CPI_PASSTHROUGH_PATTERNS: &[&str] = &[
    "invoke",
    "invoke_signed",
    "CpiContext",
    "with_remaining_accounts",
    "AccountMeta",
];

/// Tokens that indicate account *data* (not just its pubkey/is_signer) is read
/// or written locally. If none of these appear, the handler never trusts the
/// contents of a remaining account, so it cannot exhibit the SOL-013 defect.
const DATA_ACCESS_PATTERNS: &[&str] = &[
    "try_borrow_data",
    "try_borrow_mut_data",
    "borrow_data",
    "borrow_mut",
    ". data",
    "lamports",
    "deserialize",
    "unpack",
];

struct RemainingAccountsVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    fn_bodies: HashMap<String, String>,
}

impl<'a> RemainingAccountsVisitor<'a> {
    /// FP: validation delegated to a helper (`validate_oracle_account(acc)?`).
    /// Only suppress when we can RESOLVE the callee's body in this file AND
    /// confirm it actually contains a real check token — never a blanket
    /// name-based skip (that would create false negatives on stub helpers).
    fn delegates_validation(&self, body_src: &str, current_fn: &str) -> bool {
        for (name, helper_body) in &self.fn_bodies {
            if name == current_fn {
                continue;
            }
            // The callee must look like a validation routine by name...
            let lname = name.to_lowercase();
            let intent = lname.contains("validate")
                || lname.contains("verify")
                || lname.contains("check")
                || lname.contains("assert")
                || lname.contains("ensure");
            if !intent {
                continue;
            }
            // ...it must actually be called from this handler...
            if !body_src.contains(&format!("{} (", name)) {
                continue;
            }
            // ...and its resolved body must contain a genuine validation token.
            if SAFE_PATTERNS.iter().any(|p| helper_body.contains(p)) {
                return true;
            }
        }
        false
    }
}

impl<'ast, 'a> Visit<'ast> for RemainingAccountsVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Skip `#[cfg(test)]` modules entirely — test scaffolding is not product code.
        if has_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (#[test], #[tokio::test], #[ink::test], test_*, *_test).
        if is_test_fn(func) {
            return;
        }

        let fn_name = func.sig.ident.to_string();
        let body_src = fn_body_source(func);

        if !body_src.contains("remaining_accounts") {
            return;
        }

        // 1. Direct, in-body validation patterns (owner/key/discriminator/asserts).
        if SAFE_PATTERNS.iter().any(|p| body_src.contains(p)) {
            return;
        }

        // 2. Validation delegated to a resolved helper in this file.
        if self.delegates_validation(&body_src, &fn_name) {
            return;
        }

        let reads_data = DATA_ACCESS_PATTERNS.iter().any(|p| body_src.contains(p));

        // 3. Pure CPI passthrough: accounts are only forwarded to invoke /
        //    CpiContext / AccountMeta construction and never read locally. The
        //    invoked program performs its own owner/key validation.
        let is_cpi_passthrough = CPI_PASSTHROUGH_PATTERNS
            .iter()
            .any(|p| body_src.contains(p));
        if is_cpi_passthrough && !reads_data {
            return;
        }

        // 4. Require an actual dangerous use of the accounts. A handler that only
        //    checks cardinality (`.len()` / `.is_empty()`) and rejects/accepts —
        //    without ever iterating, indexing, or reading account data — cannot
        //    exhibit the vulnerability. Real vulns necessarily read/iterate the
        //    unvalidated accounts, so recall is unaffected.
        if !uses_accounts_dangerously(&body_src, reads_data) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-013".to_string(),
            name: "unsafe-remaining-accounts".to_string(),
            severity: Severity::High,
            confidence: Confidence::Medium,
            message: format!(
                "Function '{}' uses ctx.remaining_accounts without owner/type/key validation",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Validate remaining_accounts by checking owner, deserializing with try_from/try_deserialize, or verifying keys with require_keys_eq!".to_string(),
            chain: Chain::Solana,
        });
    }
}

/// Whether the body actually uses the accounts in a way that could trust their
/// contents: iterating, indexing, element accessors, a `for` loop, or a direct
/// data/lamport read. Pure `.len()`/`.is_empty()` cardinality checks do not count.
fn uses_accounts_dangerously(body_src: &str, reads_data: bool) -> bool {
    if reads_data {
        return true;
    }
    body_src.contains(". iter")
        || body_src.contains(". into_iter")
        || body_src.contains("for ")
        || body_src.contains("remaining_accounts [")
        || body_src.contains(". get (")
        || body_src.contains(". first")
        || body_src.contains(". last")
        || body_src.contains(". split_at")
}

/// Collect the token-stream body of every function (free fns and impl methods)
/// in the file, keyed by identifier, for intra-file helper resolution.
fn collect_fn_bodies(ast: &syn::File) -> HashMap<String, String> {
    struct Collector {
        bodies: HashMap<String, String>,
    }
    impl<'ast> Visit<'ast> for Collector {
        fn visit_item_fn(&mut self, f: &'ast ItemFn) {
            self.bodies
                .entry(f.sig.ident.to_string())
                .or_insert_with(|| f.block.to_token_stream().to_string());
            syn::visit::visit_item_fn(self, f);
        }
        fn visit_impl_item_fn(&mut self, f: &'ast ImplItemFn) {
            self.bodies
                .entry(f.sig.ident.to_string())
                .or_insert_with(|| f.block.to_token_stream().to_string());
            syn::visit::visit_impl_item_fn(self, f);
        }
    }
    let mut c = Collector {
        bodies: HashMap::new(),
    };
    c.visit_file(ast);
    c.bodies
}

/// Whether a function is a test function.
fn is_test_fn(func: &ItemFn) -> bool {
    let n = func.sig.ident.to_string();
    if n.starts_with("test_") || n.ends_with("_test") {
        return true;
    }
    // Matches #[test], #[tokio::test], #[ink::test], etc. (last path segment == "test").
    func.attrs.iter().any(|a| {
        a.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

/// Whether an attribute list carries `#[cfg(test)]`.
fn has_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| {
        a.path().is_ident("cfg") && a.meta.to_token_stream().to_string().contains("test")
    })
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
        RemainingAccountsDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_remaining_accounts_without_validation() {
        let source = r#"
            fn process_swap(ctx: Context<Swap>) {
                for account in ctx.remaining_accounts.iter() {
                    let data = account.try_borrow_data()?;
                    process_data(&data);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect remaining_accounts without validation"
        );
        assert_eq!(findings[0].detector_id, "SOL-013");
    }

    #[test]
    fn test_no_finding_with_owner_check() {
        let source = r#"
            fn process_swap(ctx: Context<Swap>) {
                for account in ctx.remaining_accounts.iter() {
                    if account.owner != &spl_token::ID {
                        return Err(ErrorCode::InvalidOwner.into());
                    }
                    let data = account.try_borrow_data()?;
                    process_data(&data);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when owner check is present"
        );
    }

    #[test]
    fn test_no_finding_with_cpi_passthrough() {
        let source = r#"
            fn forward_accounts(ctx: Context<Forward>) {
                let cpi_ctx = CpiContext::new(ctx.accounts.program.to_account_info(), Transfer {})
                    .with_remaining_accounts(ctx.remaining_accounts.to_vec());
                invoke(cpi_ctx)?;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag CPI passthrough of remaining_accounts"
        );
    }

    // --- FP regression tests (should NOT flag) ---

    // FP idx 0: negated method-call key comparison with early-return Err.
    #[test]
    fn test_no_finding_with_negated_key_check() {
        let source = r#"
            fn process(ctx: Context<Swap>) -> Result<()> {
                for account in ctx.remaining_accounts.iter() {
                    if account.key() != &EXPECTED_ORACLE {
                        return Err(ErrorCode::InvalidOracle.into());
                    }
                    let data = account.try_borrow_data()?;
                    process_data(&data);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a negated key() comparison guard"
        );
    }

    // FP idx 1: validation delegated to a resolvable helper that really checks.
    #[test]
    fn test_no_finding_with_delegated_validation_helper() {
        let source = r#"
            fn validate_oracle_account(account: &AccountInfo) -> Result<()> {
                if account.owner != &crate::ID {
                    return Err(ErrorCode::InvalidOwner.into());
                }
                Ok(())
            }

            fn process(ctx: Context<Swap>) -> Result<()> {
                for account in ctx.remaining_accounts.iter() {
                    validate_oracle_account(account)?;
                    let data = account.try_borrow_data()?;
                    process_data(&data);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when validation is delegated to a resolved helper"
        );
    }

    // Soundness guard for FP idx 1: an unresolved / non-validating helper must
    // still fire (no blanket name-based skip).
    #[test]
    fn test_still_flags_when_helper_does_not_validate() {
        let source = r#"
            fn check_something(account: &AccountInfo) -> Result<()> {
                msg!("no real validation here");
                Ok(())
            }

            fn process(ctx: Context<Swap>) -> Result<()> {
                for account in ctx.remaining_accounts.iter() {
                    check_something(account)?;
                    let data = account.try_borrow_data()?;
                    process_data(&data);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A validation-named helper that performs no real check must not suppress the finding"
        );
    }

    // FP idx 2: pure CPI passthrough that builds AccountMetas then invokes.
    #[test]
    fn test_no_finding_with_accountmeta_passthrough() {
        let source = r#"
            fn forward(ctx: Context<Forward>) -> Result<()> {
                let metas: Vec<AccountMeta> = ctx.remaining_accounts
                    .iter()
                    .map(|a| AccountMeta::new_readonly(*a.key, a.is_signer))
                    .collect();
                let ix = Instruction { program_id: TARGET_ID, accounts: metas, data: vec![] };
                invoke(&ix, ctx.remaining_accounts)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag AccountMeta-building CPI passthrough"
        );
    }

    // FP idx 3: vipers assert_keys_eq! macro.
    #[test]
    fn test_no_finding_with_assert_keys_eq() {
        let source = r#"
            fn process(ctx: Context<Swap>) -> Result<()> {
                let acc = &ctx.remaining_accounts[0];
                assert_keys_eq!(acc.key, EXPECTED_MINT, InvalidMint);
                let data = acc.try_borrow_data()?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when assert_keys_eq! validates the key"
        );
    }

    // FP idx 4: native AccountInfo.key field comparison (no parens).
    #[test]
    fn test_no_finding_with_native_key_field_check() {
        let source = r#"
            fn process(ctx: Context<Swap>) -> Result<()> {
                let acc = ctx.remaining_accounts.iter()
                    .find(|a| a.key == &EXPECTED)
                    .ok_or(ErrorCode::Missing)?;
                let data = acc.try_borrow_data()?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag native .key field equality checks"
        );
    }

    // FP idx 5: guard that only rejects extra accounts, never reads them.
    #[test]
    fn test_no_finding_with_cardinality_only_guard() {
        let source = r#"
            fn process(ctx: Context<Swap>) -> Result<()> {
                if !ctx.remaining_accounts.is_empty() {
                    return Err(ErrorCode::TooManyAccounts.into());
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a cardinality-only guard that never reads accounts"
        );
    }
}
