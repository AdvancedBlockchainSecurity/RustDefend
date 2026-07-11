use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct InitIfNeededDetector;

impl Detector for InitIfNeededDetector {
    fn id(&self) -> &'static str {
        "SOL-014"
    }
    fn name(&self) -> &'static str {
        "init-if-needed-reinitialization"
    }
    fn description(&self) -> &'static str {
        "Detects Anchor init_if_needed constraint without guard checks against reinitialization"
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
        // Skip test files
        let path_str = ctx.file_path.to_string_lossy();
        if path_str.contains("/tests/") || path_str.ends_with("_test.rs") {
            return Vec::new();
        }

        // Require Anchor-specific source markers — init_if_needed is an Anchor feature
        if !ctx.source.contains("anchor_lang")
            && !ctx.source.contains("Anchor")
            && !ctx.source.contains("#[account(")
            && !ctx.source.contains("#[derive(Accounts)]")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = InitIfNeededVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const SAFE_PATTERNS: &[&str] = &[
    "is_initialized",
    "initialized",
    "AlreadyInitialized",
    "AccountAlreadyInitialized",
    "already_initialized",
    // Value-based reinitialization guards that are semantically equivalent to an
    // is_initialized check. A freshly created init_if_needed account is zero-filled,
    // so handlers frequently reject an already-populated account by comparing a key
    // field against its default / checking the raw account data. These are strong,
    // specific reinit-guard idioms (token-stream stringification inserts spaces
    // around `::`, hence "Pubkey :: default").
    "Pubkey :: default",
    "data_is_empty",
];

const SAFE_ACCOUNT_TYPES: &[&str] = &["TokenAccount", "AssociatedTokenAccount", "Mint"];

/// Recursively determine whether `tokens` contains a standalone identifier equal to
/// `target`. Unlike a substring search over the stringified token stream, this ignores:
///   - doc comments (`///` becomes `#[doc = "..."]`, whose text is a string literal),
///   - string / message literals (e.g. `msg!("... init_if_needed")`),
///   - identifiers that merely contain the target as a substring (e.g.
///     `allow_init_if_needed`, which is a single distinct `Ident`).
fn tokens_contain_ident(tokens: TokenStream, target: &str) -> bool {
    tokens.into_iter().any(|tt| match tt {
        TokenTree::Ident(id) => id == target,
        TokenTree::Group(g) => tokens_contain_ident(g.stream(), target),
        _ => false,
    })
}

/// Match test attributes by their last path segment so `#[test]`, `#[tokio::test]`,
/// `#[ink::test]`, and `#[async_std::test]` are all recognized as test functions.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

struct InitIfNeededVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for InitIfNeededVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Skip #[cfg(test)] modules entirely. Test-only code is compiled only for the
        // test harness and is never part of the deployed on-chain program, so it has no
        // attack surface. The detector already skips /tests/ paths and #[test] fns; this
        // covers the common in-file `#[cfg(test)] mod tests { ... }` layout, including
        // helper fns (e.g. fixtures) that carry no test attribute or naming.
        if has_attribute_with_value(&node.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions (name-based and attribute-based, incl. tokio::test etc.)
        if fn_name.starts_with("test_") || fn_name.ends_with("_test") || is_test_fn(&func.attrs) {
            return;
        }

        // Trigger only on a genuine `init_if_needed` identifier token. This ignores doc
        // comments, string-literal contents, and identifiers that merely embed the
        // substring (e.g. `allow_init_if_needed`).
        if !tokens_contain_ident(func.to_token_stream(), "init_if_needed") {
            return;
        }

        let fn_src = func.to_token_stream().to_string();

        // Check if the init_if_needed is on a token account type (safe)
        let has_safe_type = SAFE_ACCOUNT_TYPES.iter().any(|t| {
            // Look for init_if_needed near the safe account type in the attribute
            let src = &fn_src;
            if let Some(pos) = src.find("init_if_needed") {
                // Check surrounding context (within ~200 chars)
                let start = pos.saturating_sub(100);
                let end = (pos + 200).min(src.len());
                let context = &src[start..end];
                context.contains(t)
            } else {
                false
            }
        });

        if has_safe_type {
            return;
        }

        // Check for safe guard patterns in function body and surrounding source
        let body_src = fn_body_source(func);
        let has_guard = SAFE_PATTERNS
            .iter()
            .any(|p| body_src.contains(p) || fn_src.contains(p));

        // Also check for constraint = in the same attribute block as init_if_needed
        let has_constraint = {
            if let Some(pos) = fn_src.find("init_if_needed") {
                let start = pos.saturating_sub(200);
                let end = (pos + 300).min(fn_src.len());
                let context = &fn_src[start..end];
                context.contains("constraint =")
            } else {
                false
            }
        };

        if has_guard || has_constraint {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-014".to_string(),
            name: "init-if-needed-reinitialization".to_string(),
            severity: Severity::High,
            confidence: Confidence::Medium,
            message: format!(
                "Function '{}' uses init_if_needed without reinitialization guard",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add an is_initialized check or constraint to prevent reinitialization attacks when using init_if_needed".to_string(),
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
        InitIfNeededDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_init_if_needed_without_guard() {
        let source = r#"
            fn initialize_user(ctx: Context<InitUser>) {
                // #[account(init_if_needed, payer = user, space = 8 + UserData::LEN)]
                let user_data = &mut ctx.accounts.user_data;
                user_data.init_if_needed;
                user_data.authority = ctx.accounts.user.key();
                user_data.balance = 0;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect init_if_needed without guard"
        );
        assert_eq!(findings[0].detector_id, "SOL-014");
    }

    #[test]
    fn test_no_finding_with_is_initialized_check() {
        let source = r#"
            fn initialize_user(ctx: Context<InitUser>) {
                // #[account(init_if_needed, payer = user, space = 8 + UserData::LEN)]
                let user_data = &mut ctx.accounts.user_data;
                user_data.init_if_needed;
                if user_data.is_initialized {
                    return Err(ErrorCode::AlreadyInitialized.into());
                }
                user_data.authority = ctx.accounts.user.key();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when is_initialized check present"
        );
    }

    #[test]
    fn test_no_finding_with_token_account() {
        let source = r#"
            fn initialize_ata(ctx: Context<InitAta>) {
                // TokenAccount is safe - token program manages state
                let ata: Account<TokenAccount> = ctx.accounts.init_if_needed;
                let balance = ata.amount;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag TokenAccount with init_if_needed"
        );
    }

    // FP 0: The literal `init_if_needed` reaches the function token stream only through a
    // doc comment; the real reinit guard (`has_one = authority`) lives on the Accounts
    // struct. The handler body performs no unguarded init. Must NOT flag.
    #[test]
    fn test_no_finding_doc_comment_mentions_init_if_needed() {
        let source = r#"
            /// The profile account uses init_if_needed in CreateProfile;
            /// reinit is prevented there by `has_one = authority`.
            pub fn create_profile(ctx: Context<CreateProfile>) -> Result<()> {
                let p = &mut ctx.accounts.profile;
                p.authority = ctx.accounts.user.key();
                Ok(())
            }

            #[derive(Accounts)]
            pub struct CreateProfile<'info> {
                #[account(init_if_needed, payer = user, space = 8 + Profile::LEN, has_one = authority)]
                pub profile: Account<'info, Profile>,
                #[account(mut)]
                pub user: Signer<'info>,
                pub authority: Signer<'info>,
                pub system_program: Program<'info, System>,
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when init_if_needed only appears in a doc comment"
        );
    }

    // FP 1: `allow_init_if_needed` is a single identifier that merely embeds the substring.
    // The admin setter creates/initializes no account. Must NOT flag.
    #[test]
    fn test_no_finding_identifier_substring() {
        let source = r#"
            use anchor_lang::prelude::*;

            pub fn set_config(ctx: Context<SetConfig>, allow_init_if_needed: bool) -> Result<()> {
                ctx.accounts.config.allow_init_if_needed = allow_init_if_needed;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag identifiers that merely contain init_if_needed as a substring"
        );
    }

    // FP 2: `init_if_needed` appears only inside a string literal (log message). Must NOT flag.
    #[test]
    fn test_no_finding_string_literal_only() {
        let source = r#"
            use anchor_lang::prelude::*;

            pub fn migrate(ctx: Context<Migrate>) -> Result<()> {
                msg!("account created via plain init, not init_if_needed");
                ctx.accounts.registry.version = 2;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag init_if_needed occurring only inside a string literal"
        );
    }

    // FP 3: A genuine hand-rolled reinit guard expressed as `Pubkey::default()` comparison,
    // rather than an is_initialized name. Must NOT flag.
    #[test]
    fn test_no_finding_pubkey_default_guard() {
        let source = r#"
            use anchor_lang::prelude::*;

            pub fn create_pool(ctx: Context<CreatePool>) -> Result<()> {
                let pool = &mut ctx.accounts.pool;
                pool.init_if_needed;
                require!(pool.authority == Pubkey::default(), ErrorCode::PoolExists);
                pool.authority = ctx.accounts.payer.key();
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a Pubkey::default() reinit guard is present"
        );
    }

    // FP 4: In-file `#[cfg(test)]` module with an untagged helper fn and a `#[tokio::test]`.
    // Test-only code has no on-chain attack surface. Must NOT flag.
    #[test]
    fn test_no_finding_cfg_test_module() {
        let source = r#"
            use anchor_lang::prelude::*;

            #[cfg(test)]
            mod tests {
                async fn setup_fixture() {
                    let fixture = build();
                    let _ = fixture.init_if_needed;
                }

                #[tokio::test]
                async fn creates_account_when_needed() {
                    let pt = setup_fixture().await;
                    let _ = pt.init_if_needed;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag init_if_needed inside a #[cfg(test)] module"
        );
    }
}
