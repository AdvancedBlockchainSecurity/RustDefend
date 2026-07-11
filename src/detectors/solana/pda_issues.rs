use std::collections::HashMap;

use syn::visit::Visit;
use syn::{Block, Expr, ExprCall, ExprMethodCall, Attribute, ItemFn, ItemMod, Member};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct PdaIssuesDetector;

impl Detector for PdaIssuesDetector {
    fn id(&self) -> &'static str {
        "SOL-007"
    }
    fn name(&self) -> &'static str {
        "pda-bump-misuse"
    }
    fn description(&self) -> &'static str {
        "Detects create_program_address with user-provided bump seeds"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        // Map of function name -> body token source for callee resolution.
        // Used to soundly confirm that a helper actually derives the canonical
        // bump (via find_program_address) before we suppress a finding.
        let fn_bodies = collect_fn_bodies(&ctx.ast);
        let mut visitor = PdaVisitor {
            findings: &mut findings,
            ctx,
            fn_bodies: &fn_bodies,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct PdaVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    fn_bodies: &'a HashMap<String, String>,
}

impl<'ast, 'a> Visit<'ast> for PdaVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Never scan #[cfg(test)] modules: test code is compiled out of the
        // deployed BPF program and poses no on-chain attack surface.
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (#[test] / #[tokio::test] / #[ink::test] / ...)
        // and any function annotated with #[cfg(test)].
        if is_test_fn(&func.attrs) {
            return;
        }

        // Only consider ACTUAL create_program_address call sites (parsed from
        // the AST), so that mentions inside string literals / msg! macros do
        // not trigger a finding.
        let cpa_calls = collect_cpa_calls(&func.block);
        if cpa_calls.is_empty() {
            return;
        }

        let body_src = fn_body_source(func);

        // Safe: the canonical bump is derived in-body via find_program_address.
        if body_src.contains("find_program_address") {
            return;
        }

        // Safe: Anchor's ctx.bumps (field access `.bumps`) exposes the
        // canonical bump computed by find_program_address inside macro-generated
        // code. Treat any use of `.bumps` in the handler body as equivalent.
        if body_uses_bumps(&func.block) {
            return;
        }

        // Safe: a helper reachable from this function derives the canonical bump
        // (contains find_program_address). We resolve the callee's body from the
        // same-file function map rather than trusting the name blindly.
        if self.callee_derives_canonical_bump(func) {
            return;
        }

        // Only flag when at least one create_program_address call uses a bump
        // that is NOT sourced from program-owned account state. A bump read from
        // an account field (`vault.bump`, `ctx.accounts.x.bump`) or `ctx.bumps`
        // is canonical-by-construction and safe to re-derive with.
        let has_unsafe_bump = cpa_calls.iter().any(|c| !call_uses_stored_bump(c));
        if !has_unsafe_bump {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-007".to_string(),
            name: "pda-bump-misuse".to_string(),
            severity: Severity::High,
            confidence: Confidence::High,
            message: format!(
                "Function '{}' uses create_program_address without find_program_address (user-provided bump)",
                func.sig.ident
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Use find_program_address() which returns the canonical bump, or verify the provided bump against find_program_address result".to_string(),
            chain: Chain::Solana,
        });
    }
}

impl<'a> PdaVisitor<'a> {
    /// Returns true if any function called from `func`'s body resolves (in the
    /// same file) to a helper whose body derives the canonical bump via
    /// find_program_address. This soundly captures the "bump validated by a
    /// helper" pattern without a blanket name-based skip.
    fn callee_derives_canonical_bump(&self, func: &ItemFn) -> bool {
        let self_name = func.sig.ident.to_string();
        for name in collect_called_names(&func.block) {
            if name == self_name {
                continue;
            }
            if let Some(body) = self.fn_bodies.get(&name) {
                if body.contains("find_program_address") {
                    return true;
                }
            }
        }
        false
    }
}

/// Build a map of function name -> body token source for every `fn` item in the
/// file (including those nested in modules).
fn collect_fn_bodies(ast: &syn::File) -> HashMap<String, String> {
    let mut collector = FunctionCollector {
        functions: Vec::new(),
    };
    collector.visit_file(ast);
    let mut map = HashMap::new();
    for f in collector.functions {
        map.insert(f.sig.ident.to_string(), fn_body_source(&f));
    }
    map
}

/// Collect the actual `create_program_address` call expressions in a block.
/// Only real call/method-call sites are collected; string-literal or macro-token
/// mentions are ignored because syn does not visit opaque macro tokens.
fn collect_cpa_calls(block: &Block) -> Vec<Expr> {
    struct V {
        calls: Vec<Expr>,
    }
    impl<'ast> Visit<'ast> for V {
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Expr::Path(p) = node.func.as_ref() {
                if p
                    .path
                    .segments
                    .last()
                    .map(|s| s.ident == "create_program_address")
                    .unwrap_or(false)
                {
                    self.calls.push(Expr::Call(node.clone()));
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            if node.method == "create_program_address" {
                self.calls.push(Expr::MethodCall(node.clone()));
            }
            syn::visit::visit_expr_method_call(self, node);
        }
    }
    let mut v = V { calls: Vec::new() };
    v.visit_block(block);
    v.calls
}

/// Returns true if the given call expression sources its bump from program-owned
/// account state: a field access whose member is `bump`/`bumps` (e.g.
/// `vault.bump`, `ctx.accounts.vault.bump`, `ctx.bumps.vault`) or an accessor
/// method `.bump()`/`.bumps()`. These bumps are canonical-by-construction.
fn call_uses_stored_bump(expr: &Expr) -> bool {
    struct V {
        found: bool,
    }
    impl<'ast> Visit<'ast> for V {
        fn visit_expr_field(&mut self, node: &'ast syn::ExprField) {
            if let Member::Named(id) = &node.member {
                if id == "bump" || id == "bumps" {
                    self.found = true;
                }
            }
            syn::visit::visit_expr_field(self, node);
        }
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            if node.method == "bump" || node.method == "bumps" {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, node);
        }
    }
    let mut v = V { found: false };
    v.visit_expr(expr);
    v.found
}

/// Returns true if the block references Anchor's `ctx.bumps` (any field access
/// whose member is `bumps`).
fn body_uses_bumps(block: &Block) -> bool {
    struct V {
        found: bool,
    }
    impl<'ast> Visit<'ast> for V {
        fn visit_expr_field(&mut self, node: &'ast syn::ExprField) {
            if let Member::Named(id) = &node.member {
                if id == "bumps" {
                    self.found = true;
                }
            }
            syn::visit::visit_expr_field(self, node);
        }
    }
    let mut v = V { found: false };
    v.visit_block(block);
    v.found
}

/// Collect the names of functions/methods called directly within a block.
fn collect_called_names(block: &Block) -> Vec<String> {
    struct V {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for V {
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Expr::Path(p) = node.func.as_ref() {
                if let Some(seg) = p.path.segments.last() {
                    self.names.push(seg.ident.to_string());
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            self.names.push(node.method.to_string());
            syn::visit::visit_expr_method_call(self, node);
        }
    }
    let mut v = V { names: Vec::new() };
    v.visit_block(block);
    v.names
}

/// Whether a function should be treated as test-only code.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    has_attribute(attrs, "test")
        || has_attribute(attrs, "tokio::test")
        || has_attribute(attrs, "ink::test")
        || has_attribute(attrs, "async_std::test")
        || is_cfg_test(attrs)
}

/// Whether an item carries `#[cfg(test)]`.
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    has_attribute_with_value(attrs, "cfg", "test")
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
        PdaIssuesDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_user_bump() {
        let source = r#"
            fn verify_pda(bump: u8, seeds: &[u8], program_id: &Pubkey) {
                let pda = Pubkey::create_program_address(&[seeds, &[bump]], program_id).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect user-provided bump");
    }

    #[test]
    fn test_no_finding_with_find() {
        let source = r#"
            fn verify_pda(seeds: &[u8], program_id: &Pubkey) {
                let (pda, bump) = Pubkey::find_program_address(&[seeds], program_id);
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag find_program_address");
    }

    // FP idx 0: canonical bump stored in program-owned account state.
    #[test]
    fn test_no_finding_stored_account_bump() {
        let source = r#"
            fn withdraw(ctx: Context<Withdraw>, amount: u64) -> Result<()> {
                let vault = &ctx.accounts.vault;
                let expected = Pubkey::create_program_address(
                    &[b"vault", vault.owner.as_ref(), &[vault.bump]],
                    ctx.program_id,
                )?;
                require_keys_eq!(expected, vault.key(), ErrorCode::InvalidVault);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag bump read from account state (vault.bump)"
        );
    }

    // FP idx 1: Anchor ctx.bumps canonical bump.
    #[test]
    fn test_no_finding_ctx_bumps() {
        let source = r#"
            pub fn initialize(ctx: Context<Initialize>) -> Result<()> {
                let bump = ctx.bumps.vault;
                ctx.accounts.vault.bump = bump;
                let addr = Pubkey::create_program_address(&[b"vault", &[bump]], ctx.program_id)?;
                msg!("vault pda: {}", addr);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag Anchor ctx.bumps canonical bump"
        );
    }

    // FP idx 2: bump validated by a resolvable helper function.
    #[test]
    fn test_no_finding_helper_validates_bump() {
        let source = r#"
            fn assert_canonical(seeds: &[&[u8]], bump: u8, program_id: &Pubkey) -> Result<()> {
                let (_, canonical) = Pubkey::find_program_address(seeds, program_id);
                require!(bump == canonical, ErrorCode::NonCanonicalBump);
                Ok(())
            }

            fn verify_vault(bump: u8, owner: &Pubkey, program_id: &Pubkey, expected: &Pubkey) -> Result<()> {
                assert_canonical(&[b"vault", owner.as_ref()], bump, program_id)?;
                let pda = Pubkey::create_program_address(&[b"vault", owner.as_ref(), &[bump]], program_id)?;
                require_keys_eq!(pda, *expected);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a resolvable helper derives the canonical bump"
        );
    }

    // FP idx 3: create_program_address only mentioned in a string literal.
    #[test]
    fn test_no_finding_string_literal() {
        let source = r#"
            fn reject_manual_pda() -> Result<()> {
                msg!("create_program_address is not allowed here; PDAs are derived at init");
                Err(ErrorCode::Unsupported.into())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag string-literal mentions of create_program_address"
        );
    }

    // FP idx 4: findings on #[cfg(test)] / #[test] functions.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;
                #[test]
                fn create_program_address_rejects_bad_bump() {
                    let err = Pubkey::create_program_address(&[b"vault", &[0u8]], &crate::ID);
                    assert!(err.is_err());
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag create_program_address in #[cfg(test)] code"
        );
    }
}
