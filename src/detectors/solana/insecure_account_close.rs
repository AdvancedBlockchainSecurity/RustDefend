use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct InsecureAccountCloseDetector;

impl Detector for InsecureAccountCloseDetector {
    fn id(&self) -> &'static str {
        "SOL-005"
    }
    fn name(&self) -> &'static str {
        "insecure-account-close"
    }
    fn description(&self) -> &'static str {
        "Detects account closure that doesn't zero data and set discriminator"
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

        let mut findings = Vec::new();
        let mut visitor = CloseVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// True if the function/module carries a test attribute (`#[test]`,
/// `#[tokio::test]`, `#[ink::test]`, or `#[cfg(test)]`). Test scaffolding is
/// compiled only for host-side unit tests and has no on-chain revival-attack
/// surface, so it must never be flagged.
fn is_test_attributed(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let path = attr.path();
        // Any attribute path whose final segment is `test`
        // (covers `#[test]`, `#[tokio::test]`, `#[ink::test]`, etc.).
        if path
            .segments
            .last()
            .map_or(false, |seg| seg.ident == "test")
        {
            return true;
        }
        // `#[cfg(test)]`
        if path.is_ident("cfg") {
            let tokens = attr.meta.to_token_stream().to_string();
            return tokens.contains("test");
        }
        false
    })
}

/// True if the token-stream body contains a genuine zero-assignment to a
/// lamport balance (e.g. `**acc.lamports.borrow_mut() = 0` or
/// `**acc.try_borrow_mut_lamports()? = 0`).
///
/// In proc_macro2 token-stream rendering a real assignment `=` is a lone token
/// surrounded by spaces (`" = 0"`), whereas comparisons and compound
/// assignments render as `" == 0"`, `" != 0"`, `" += 0"`, `" -= 0"`, etc., none
/// of which contain the substring `" = 0"`. We additionally require the word
/// `lamports` to appear shortly before the assignment so that unrelated
/// zero-initialized locals (`let mut total = 0;`) in a plain transfer function
/// are not mistaken for a closure.
fn has_lamport_zero_assignment(body: &str) -> bool {
    const NEEDLE: &str = " = 0";
    let mut search_start = 0;
    while let Some(rel) = body[search_start..].find(NEEDLE) {
        let idx = search_start + rel;
        let after = idx + NEEDLE.len();
        // Ensure the literal is exactly `0` (not `0u64`, `0x..`, `0.0`, etc.).
        let after_ok = body[after..]
            .chars()
            .next()
            .map_or(true, |c| !c.is_ascii_alphanumeric() && c != '.' && c != '_');
        if after_ok {
            // Look back a bounded window for a lamports target, snapping to a
            // char boundary to stay panic-safe on non-ASCII bodies.
            let mut win_start = idx.saturating_sub(60);
            while win_start < idx && !body.is_char_boundary(win_start) {
                win_start += 1;
            }
            if body[win_start..idx].contains("lamports") {
                return true;
            }
        }
        search_start = idx + NEEDLE.len();
    }
    false
}

struct CloseVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for CloseVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Do not descend into `#[cfg(test)]` modules — their close-like helpers
        // are test scaffolding, not deployable program logic.
        if is_test_attributed(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (`#[test]`, `#[tokio::test]`, `#[ink::test]`, ...).
        if is_test_attributed(&func.attrs) {
            return;
        }

        let fn_src = func.to_token_stream().to_string();

        // Skip Anchor close = recipient pattern
        if fn_src.contains("close =") || fn_src.contains("close=") {
            return;
        }

        let body_src = fn_body_source(func);

        // Require an actual zero-assignment to lamports (account-drain closure
        // pattern). Plain transfers/withdrawals (`+=`/`-=`) and read-only
        // balance checks (`== 0`, `!= 0`) are not closures and must not match.
        if !has_lamport_zero_assignment(&body_src) {
            return;
        }

        // Check if the account data is also invalidated. This covers the
        // classic byte-zeroing / discriminator idioms as well as the modern,
        // currently-recommended close idiom (reassign ownership to the System
        // Program + realloc the data to zero length) and Anchor's close()
        // helper.
        let has_data_zero =
            // Byte-zeroing via fill(0), fill(0u8), fill(0_u8), ... on any receiver.
            body_src.contains(". fill (0")
            || body_src.contains("fill(0)")
            || body_src.contains("sol_memset")
            || body_src.contains("CLOSED_ACCOUNT_DISCRIMINATOR")
            // Zeroing the data buffer via an iterator or bulk copy.
            || (body_src.contains("iter_mut") && body_src.contains("data"))
            || (body_src.contains("copy_from_slice") && body_src.contains("data"))
            // Modern recommended close: assign to system program + realloc(0).
            || body_src.contains("realloc (0")
            || (body_src.contains(". assign") && body_src.contains("system_program"))
            // Anchor's AccountsClose::close() helper.
            || body_src.contains(". close (");

        if !has_data_zero {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "SOL-005".to_string(),
                name: "insecure-account-close".to_string(),
                severity: Severity::High,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' closes account by zeroing lamports without clearing data/discriminator",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "After zeroing lamports, also zero account data and set the discriminator to CLOSED_ACCOUNT_DISCRIMINATOR, or use Anchor's #[account(close = recipient)]".to_string(),
                chain: Chain::Solana,
            });
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
        InsecureAccountCloseDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_insecure_close() {
        let source = r#"
            fn close_account(account: &AccountInfo, dest: &AccountInfo) {
                let dest_lamports = dest.lamports();
                **dest.lamports.borrow_mut() = dest_lamports + account.lamports();
                **account.lamports.borrow_mut() = 0;
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect insecure account close");
    }

    #[test]
    fn test_no_finding_with_data_zero() {
        let source = r#"
            fn close_account(account: &AccountInfo, dest: &AccountInfo) {
                **dest.lamports.borrow_mut() += account.lamports();
                **account.lamports.borrow_mut() = 0;
                account.data.borrow_mut().fill(0);
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag when data is zeroed");
    }

    // FP idx 0: plain lamport transfer/withdraw is not a closure.
    #[test]
    fn test_no_finding_plain_transfer() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;

            fn withdraw(vault: &AccountInfo, user: &AccountInfo, amount: u64) -> ProgramResult {
                **vault.try_borrow_mut_lamports()? -= amount;
                **user.try_borrow_mut_lamports()? += amount;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Plain lamport transfer must not be flagged as an account close"
        );
    }

    // FP idx 1: read-only lamport balance check (== 0 / != 0).
    #[test]
    fn test_no_finding_readonly_balance_check() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::program_error::ProgramError;

            fn assert_funded(account: &AccountInfo) -> ProgramResult {
                if account.lamports() == 0 {
                    return Err(ProgramError::InsufficientFunds);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Read-only balance check must not be treated as lamport zeroing"
        );
    }

    // FP idx 1 variant: reads lamports while zero-initializing an unrelated local.
    #[test]
    fn test_no_finding_unrelated_zero_local() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            fn tally(account: &AccountInfo) -> u64 {
                let mut total = 0;
                total += account.lamports();
                total
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Zero-initialized local plus lamports read must not be flagged"
        );
    }

    // FP idx 2: modern recommended close (assign to system program + realloc(0)).
    #[test]
    fn test_no_finding_modern_close_pattern() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;
            use solana_program::system_program;

            fn close(account: &AccountInfo, dest: &AccountInfo) -> ProgramResult {
                **dest.try_borrow_mut_lamports()? += account.lamports();
                **account.try_borrow_mut_lamports()? = 0;
                account.assign(&system_program::ID);
                account.realloc(0, false)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Modern assign+realloc(0) close pattern must not be flagged"
        );
    }

    // FP idx 3: data zeroed via fill(0u8) on the try_borrow_mut_data() receiver.
    #[test]
    fn test_no_finding_fill_typed_literal() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;

            fn close_account(account: &AccountInfo, dest: &AccountInfo) -> ProgramResult {
                **dest.try_borrow_mut_lamports()? += account.lamports();
                **account.try_borrow_mut_lamports()? = 0;
                account.try_borrow_mut_data()?.fill(0u8);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "fill(0u8) data zeroing must be recognized as a mitigation"
        );
    }

    // FP idx 3 variant: data zeroed via an iter_mut loop.
    #[test]
    fn test_no_finding_iter_mut_zeroing() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;

            fn close_account(account: &AccountInfo, dest: &AccountInfo) -> ProgramResult {
                **dest.try_borrow_mut_lamports()? += account.lamports();
                **account.try_borrow_mut_lamports()? = 0;
                let mut data = account.try_borrow_mut_data()?;
                for b in data.iter_mut() {
                    *b = 0;
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "iter_mut zeroing of account data must be recognized as a mitigation"
        );
    }

    // FP idx 3 variant: data zeroed via copy_from_slice.
    #[test]
    fn test_no_finding_copy_from_slice_zeroing() {
        let source = r#"
            use solana_program::account_info::AccountInfo;
            use solana_program::entrypoint::ProgramResult;

            fn close_account(account: &AccountInfo, dest: &AccountInfo) -> ProgramResult {
                **dest.try_borrow_mut_lamports()? += account.lamports();
                **account.try_borrow_mut_lamports()? = 0;
                let zeros = [0u8; 128];
                let mut data = account.try_borrow_mut_data()?;
                data.copy_from_slice(&zeros);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "copy_from_slice zeroing of account data must be recognized as a mitigation"
        );
    }

    // FP idx 4: unit-test / mock helpers inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            #[cfg(test)]
            mod tests {
                use super::*;

                fn drain_for_test(account: &AccountInfo) {
                    **account.lamports.borrow_mut() = 0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Helpers inside #[cfg(test)] modules must not be flagged"
        );
    }

    // FP idx 4 variant: a #[test] function directly.
    #[test]
    fn test_no_finding_test_function() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            #[test]
            fn drain_for_test() {
                let account: &AccountInfo = todo!();
                **account.lamports.borrow_mut() = 0;
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "#[test] functions must not be flagged");
    }
}
