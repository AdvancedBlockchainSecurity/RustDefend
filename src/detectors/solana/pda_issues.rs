use std::collections::{HashMap, HashSet};

use syn::visit::Visit;
use syn::{Attribute, Block, Expr, ExprCall, ExprMethodCall, ItemFn, ItemMod, Member};

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
        // that is NOT sourced from program-owned account state. Provenance is
        // resolved structurally from the `let` bindings in the body: a field
        // named `bump` is only canonical-by-construction when its base actually
        // roots at `ctx.accounts`/`ctx.bumps` (or a local aliasing that state).
        // A `bump` field on a Borsh-decoded instruction-data struct spells the
        // same but is fully attacker-controlled, so it must still flag.
        let prov = collect_bump_provenance(&func.block);
        let has_unsafe_bump = cpa_calls.iter().any(|c| !call_uses_stored_bump(c, &prov));
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
                if p.path
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

/// Provenance facts about the locals of a single function body, derived from
/// its `let` initializers. Neither set is keyed on how an identifier is spelled.
#[derive(Default)]
struct BumpProvenance {
    /// Locals whose value is drawn from program-owned account state, so that
    /// `vault.bump` after `let vault = &ctx.accounts.vault;` resolves.
    account_locals: HashSet<String>,
    /// Locals bound to a bump that is itself sourced from account state, so
    /// that `let bump = ctx.bumps.vault;` followed by `&[bump]` resolves.
    stored_bump_locals: HashSet<String>,
}

/// Strip references, dereferences, parens and groups to reach the underlying
/// place expression.
fn peel(expr: &Expr) -> &Expr {
    match expr {
        Expr::Reference(r) => peel(&r.expr),
        Expr::Paren(p) => peel(&p.expr),
        Expr::Group(g) => peel(&g.expr),
        Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => peel(&u.expr),
        _ => expr,
    }
}

/// Walk the base chain of a place expression down to its root identifier.
/// Returns `(root_ident, passes_through_account_state)`, where the flag records
/// whether any link in the chain is Anchor's `accounts` or `bumps` member.
fn place_root(expr: &Expr) -> Option<(String, bool)> {
    match peel(expr) {
        Expr::Path(p) => p.path.get_ident().map(|i| (i.to_string(), false)),
        Expr::Field(f) => {
            let via = matches!(&f.member, Member::Named(id) if id == "accounts" || id == "bumps");
            place_root(&f.base).map(|(root, seen)| (root, seen || via))
        }
        Expr::MethodCall(m) => place_root(&m.receiver),
        Expr::Index(i) => place_root(&i.expr),
        Expr::Try(t) => place_root(&t.expr),
        _ => None,
    }
}

/// Returns true if the place `base` denotes program-owned account state: an
/// Anchor `ctx.accounts.*` / `ctx.bumps.*` chain, or a local aliasing one.
/// `via_self` lets the caller fold the member it is inspecting into the chain
/// (so the `bumps` in `ctx.bumps` counts even though it is the outermost link).
fn base_is_account_state(base: &Expr, via_self: bool, account_locals: &HashSet<String>) -> bool {
    match place_root(base) {
        Some((root, via)) => (root == "ctx" && (via || via_self)) || account_locals.contains(&root),
        None => false,
    }
}

/// Whether `expr` draws any of its value from program-owned account state.
/// Deliberately a "contains" check so that account data reached through a
/// deserializer (`Vault::try_from_slice(&ctx.accounts.vault.data.borrow())`)
/// still counts as account-sourced.
fn expr_draws_from_account_state(expr: &Expr, account_locals: &HashSet<String>) -> bool {
    if base_is_account_state(peel(expr), false, account_locals) {
        return true;
    }
    struct V<'a> {
        account_locals: &'a HashSet<String>,
        found: bool,
    }
    impl<'ast, 'a> Visit<'ast> for V<'a> {
        fn visit_expr_field(&mut self, node: &'ast syn::ExprField) {
            let via_self =
                matches!(&node.member, Member::Named(id) if id == "accounts" || id == "bumps");
            if base_is_account_state(&node.base, via_self, self.account_locals) {
                self.found = true;
            }
            syn::visit::visit_expr_field(self, node);
        }
    }
    let mut v = V {
        account_locals,
        found: false,
    };
    v.visit_expr(expr);
    v.found
}

/// Classify every bump read inside `expr` by provenance, returning
/// `(has_stored, has_unstored)`. A bump read is a field/method access named
/// `bump`/`bumps`; it is *stored* only when its base resolves to account state.
/// A bare identifier counts as stored only when a `let` bound it to a stored
/// bump — an unknown identifier is never evidence of safety.
fn classify_bump_reads(expr: &Expr, prov: &BumpProvenance) -> (bool, bool) {
    struct V<'a> {
        prov: &'a BumpProvenance,
        stored: bool,
        unstored: bool,
    }
    impl<'ast, 'a> Visit<'ast> for V<'a> {
        fn visit_expr_field(&mut self, node: &'ast syn::ExprField) {
            if let Member::Named(id) = &node.member {
                if id == "bump" || id == "bumps" {
                    if base_is_account_state(&node.base, id == "bumps", &self.prov.account_locals) {
                        self.stored = true;
                    } else {
                        self.unstored = true;
                    }
                }
            }
            syn::visit::visit_expr_field(self, node);
        }
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            if node.method == "bump" || node.method == "bumps" {
                if base_is_account_state(&node.receiver, false, &self.prov.account_locals) {
                    self.stored = true;
                } else {
                    self.unstored = true;
                }
            }
            syn::visit::visit_expr_method_call(self, node);
        }
        fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
            if let Some(id) = node.path.get_ident() {
                if self.prov.stored_bump_locals.contains(&id.to_string()) {
                    self.stored = true;
                }
            }
            syn::visit::visit_expr_path(self, node);
        }
    }
    let mut v = V {
        prov,
        stored: false,
        unstored: false,
    };
    v.visit_expr(expr);
    (v.stored, v.unstored)
}

/// The binding name introduced by a simple `let` pattern, if any.
fn local_binding_ident(pat: &syn::Pat) -> Option<String> {
    match pat {
        syn::Pat::Ident(i) => Some(i.ident.to_string()),
        syn::Pat::Type(t) => local_binding_ident(&t.pat),
        _ => None,
    }
}

/// Resolve, in source order, which locals alias account state and which hold a
/// bump sourced from it. Rebinding a name to a non-account value retracts the
/// earlier fact, so shadowing cannot launder an attacker-controlled bump.
fn collect_bump_provenance(block: &Block) -> BumpProvenance {
    struct V {
        prov: BumpProvenance,
    }
    impl<'ast> Visit<'ast> for V {
        fn visit_local(&mut self, node: &'ast syn::Local) {
            syn::visit::visit_local(self, node);
            if let Some(name) = local_binding_ident(&node.pat) {
                if let Some(init) = node.init.as_ref() {
                    if expr_draws_from_account_state(&init.expr, &self.prov.account_locals) {
                        self.prov.account_locals.insert(name.clone());
                    } else {
                        self.prov.account_locals.remove(&name);
                    }
                    let (stored, unstored) = classify_bump_reads(&init.expr, &self.prov);
                    if stored && !unstored {
                        self.prov.stored_bump_locals.insert(name);
                    } else {
                        self.prov.stored_bump_locals.remove(&name);
                    }
                }
            }
        }
    }
    let mut v = V {
        prov: BumpProvenance::default(),
    };
    v.visit_block(block);
    v.prov
}

/// Returns true if the given call expression sources its bump from program-owned
/// account state, and from nowhere else. Requires positive evidence: a bump read
/// whose base actually roots at `ctx.accounts`/`ctx.bumps` or a local aliasing
/// that state. A call mixing a stored bump with an unstored one stays unsafe.
fn call_uses_stored_bump(expr: &Expr, prov: &BumpProvenance) -> bool {
    let (stored, unstored) = classify_bump_reads(expr, prov);
    stored && !unstored
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

    // MUST STILL FLAG: the bump arrives on a Borsh-decoded instruction-data
    // struct. `params.bump` spells exactly like a stored account bump but is
    // raw attacker-controlled input: create_program_address accepts any
    // off-curve bump, so a ground non-canonical bump yields an alternate valid
    // authority. Provenance, not the field name, is what makes a bump safe.
    #[test]
    fn test_still_flags_instruction_data_struct_bump() {
        let source = r#"
            pub fn withdraw(ctx: Context<Withdraw>, params: WithdrawParams) -> Result<()> {
                let owner_key = ctx.accounts.owner.key();
                let authority = Pubkey::create_program_address(
                    &[b"vault-authority", owner_key.as_ref(), &[params.bump]],
                    ctx.program_id,
                )
                .map_err(|_| error!(VaultError::InvalidAuthority))?;
                require_keys_eq!(
                    authority,
                    ctx.accounts.vault_authority.key(),
                    VaultError::InvalidAuthority
                );
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert_eq!(
            findings.len(),
            1,
            "Should flag a bump read from instruction data even though the field is named `bump`"
        );
    }

    // MUST STILL FLAG: renaming the field must not change the verdict. This is
    // the single-token pin from the audit — the probe and this variant differ
    // only in spelling, so they must agree.
    #[test]
    fn test_still_flags_instruction_data_bump_regardless_of_field_name() {
        let renamed = r#"
            pub fn withdraw(ctx: Context<Withdraw>, params: WithdrawParams) -> Result<()> {
                let addr = Pubkey::create_program_address(
                    &[b"vault-authority", &[params.seed_bump]],
                    ctx.program_id,
                )?;
                Ok(())
            }
        "#;
        let original = renamed.replace("seed_bump", "bump");
        assert_eq!(
            run_detector(&original).len(),
            run_detector(renamed).len(),
            "Verdict must not depend on whether the field is spelled `bump` or `seed_bump`"
        );
        assert_eq!(run_detector(&original).len(), 1, "Both must flag");
    }

    // MUST STILL FLAG: a stored bump does not launder an attacker-controlled
    // one used in the same derivation.
    #[test]
    fn test_still_flags_mixed_stored_and_user_bump() {
        let source = r#"
            fn withdraw(ctx: Context<Withdraw>, params: WithdrawParams) -> Result<()> {
                let vault = &ctx.accounts.vault;
                let addr = Pubkey::create_program_address(
                    &[b"vault", &[vault.bump], &[params.bump]],
                    ctx.program_id,
                )?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert_eq!(
            findings.len(),
            1,
            "A call mixing a stored bump with a user-provided bump is still unsafe"
        );
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
