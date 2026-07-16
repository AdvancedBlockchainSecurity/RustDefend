use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, ItemFn, ItemMod};

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

        // Build a map of every locally-defined function's body AST so that a
        // discriminator check factored out into a helper can be resolved. The
        // block is kept as syntax (not source text) because deciding whether a
        // helper *performs* a type check requires structure, not spelling.
        let mut fn_collector = FunctionCollector {
            functions: Vec::new(),
        };
        fn_collector.visit_file(&ctx.ast);
        let mut local_fn_blocks: HashMap<String, syn::Block> = HashMap::new();
        for f in &fn_collector.functions {
            local_fn_blocks
                .entry(f.sig.ident.to_string())
                .or_insert_with(|| (*f.block).clone());
        }

        let mut findings = Vec::new();
        let mut visitor = ConfusionVisitor {
            findings: &mut findings,
            ctx,
            local_fn_blocks: &local_fn_blocks,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct ConfusionVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    local_fn_blocks: &'a HashMap<String, syn::Block>,
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
        // any of them actually performs the check (the `?`/early-return
        // propagates the failure before deserialization). The helper must be
        // shown to *compare* a type tag: a helper that merely validates owner,
        // length or an init flag leaves account-type confusion wide open and
        // must not suppress the finding.
        let mut helper_checks_discriminator = false;
        for name in collect_call_names(func) {
            if name == fn_name {
                continue;
            }
            if let Some(helper_block) = self.local_fn_blocks.get(&name) {
                if block_has_discriminator_check(helper_block) {
                    helper_checks_discriminator = true;
                    break;
                }
            }
        }

        // Check for discriminator check (first 8 bytes)
        let has_discriminator = block_has_discriminator_check(&func.block)
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

/// Returns true if `block` performs a real account-type (discriminator / tag)
/// check.
///
/// This is deliberately structural rather than textual: the tag value must take
/// part in an `==`/`!=` comparison, a slice comparison (`starts_with`/`eq`), an
/// assertion condition, a `match` scrutinee, or be handed to a fallible check
/// whose failure propagates. Merely *mentioning* a tag-ish identifier is not a
/// check -- the previous substring oracle silenced this detector on genuinely
/// vulnerable code for exactly that reason.
fn block_has_discriminator_check(block: &syn::Block) -> bool {
    let mut visitor = DiscriminatorCheckVisitor { found: false };
    visitor.visit_block(block);
    visitor.found
}

/// Identifiers that name an account *type tag* (discriminator).
///
/// Initialization markers (`is_initialized`, `init_flag`, `IsInitialized`,
/// `assert_initialized`) are deliberately absent: an init flag distinguishes a
/// zeroed account from a written one, never a `Vault` from a byte-compatible
/// `UserProfile`. Treating one as the other is a false negative, not a check.
/// Likewise owner and length checks are not type checks.
fn is_type_tag_ident(ident: &str) -> bool {
    let lower = ident.to_ascii_lowercase();
    lower.contains("discriminator")
        || lower.contains("account_type")
        || lower.contains("accounttype")
        || lower.contains("type_tag")
        || lower == "tag"
        || lower.ends_with("_tag")
        || lower.starts_with("tag_")
}

/// Strip the wrappers that do not change which value an expression reads.
fn peel(expr: &Expr) -> &Expr {
    match expr {
        Expr::Paren(e) => peel(&e.expr),
        Expr::Group(e) => peel(&e.expr),
        Expr::Reference(e) => peel(&e.expr),
        other => other,
    }
}

/// Parse an expression as a `usize` literal.
fn lit_usize(expr: &Expr) -> Option<u64> {
    match peel(expr) {
        Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Int(i) => i.base10_parse::<u64>().ok(),
            _ => None,
        },
        _ => None,
    }
}

/// Returns true for a range selecting exactly the first 8 bytes: `..8`, `0..8`,
/// `..=7` or `0..=7` -- i.e. the Anchor/Borsh discriminator window.
fn is_eight_byte_prefix(expr: &Expr) -> bool {
    let range = match peel(expr) {
        Expr::Range(range) => range,
        _ => return false,
    };
    let start_ok = match &range.start {
        None => true,
        Some(start) => lit_usize(start) == Some(0),
    };
    if !start_ok {
        return false;
    }
    let end = match &range.end {
        Some(end) => match lit_usize(end) {
            Some(end) => end,
            None => return false,
        },
        None => return false,
    };
    match range.limits {
        syn::RangeLimits::HalfOpen(_) => end == 8,
        syn::RangeLimits::Closed(_) => end == 7,
    }
}

/// Returns true if `expr` reads an account type tag: a first-8-bytes window of
/// some buffer, or a path/field named after a discriminator or type tag.
fn expr_reads_type_tag(expr: &Expr) -> bool {
    match expr {
        Expr::Path(path) => path
            .path
            .segments
            .iter()
            .any(|seg| is_type_tag_ident(&seg.ident.to_string())),
        Expr::Field(field) => {
            if let syn::Member::Named(name) = &field.member {
                if is_type_tag_ident(&name.to_string()) {
                    return true;
                }
            }
            expr_reads_type_tag(&field.base)
        }
        // `data[..8]` / `data[0..8]`
        Expr::Index(index) => {
            is_eight_byte_prefix(&index.index) || expr_reads_type_tag(&index.expr)
        }
        Expr::MethodCall(call) => {
            let method = call.method.to_string();
            // `data.get(..8)`
            if matches!(method.as_str(), "get" | "get_unchecked")
                && call.args.iter().any(is_eight_byte_prefix)
            {
                return true;
            }
            if is_type_tag_ident(&method) {
                return true;
            }
            expr_reads_type_tag(&call.receiver)
        }
        // `u64::from_le_bytes(data[..8].try_into()?)`
        Expr::Call(call) => call.args.iter().any(expr_reads_type_tag),
        Expr::Reference(e) => expr_reads_type_tag(&e.expr),
        Expr::Paren(e) => expr_reads_type_tag(&e.expr),
        Expr::Group(e) => expr_reads_type_tag(&e.expr),
        Expr::Unary(e) => expr_reads_type_tag(&e.expr),
        Expr::Cast(e) => expr_reads_type_tag(&e.expr),
        Expr::Try(e) => expr_reads_type_tag(&e.expr),
        _ => false,
    }
}

/// Returns true if `mac` is an assertion whose condition mentions a type tag.
/// A macro body is an opaque token stream, so inside the condition of an
/// assertion -- which is a check by construction -- we fall back to recognising
/// the tag vocabulary and the token-stream spellings of a first-8-bytes read.
fn macro_asserts_type_tag(mac: &syn::Macro) -> bool {
    let name = match mac.path.segments.last() {
        Some(seg) => seg.ident.to_string(),
        None => return false,
    };
    let is_assertion = matches!(
        name.as_str(),
        "assert"
            | "assert_eq"
            | "assert_ne"
            | "debug_assert"
            | "debug_assert_eq"
            | "debug_assert_ne"
            | "require"
            | "require_eq"
            | "require_neq"
            | "require_keys_eq"
            | "require_keys_neq"
    );
    if !is_assertion {
        return false;
    }
    let toks = mac.tokens.to_string();
    let lower = toks.to_ascii_lowercase();
    lower.contains("discriminator")
        || lower.contains("account_type")
        || lower.contains("accounttype")
        || lower.contains("_tag")
        || toks.contains("[.. 8]")
        || toks.contains("[0 .. 8]")
        || toks.contains(". get (.. 8)")
        || toks.contains(". get (0 .. 8)")
}

/// Walks a function body looking for a structural account-type check.
struct DiscriminatorCheckVisitor {
    found: bool,
}

impl<'ast> Visit<'ast> for DiscriminatorCheckVisitor {
    fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
        // The tag must appear as an operand of an equality comparison. An
        // ordering/arithmetic operator over a tag is not a type check.
        if matches!(node.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_))
            && (expr_reads_type_tag(&node.left) || expr_reads_type_tag(&node.right))
        {
            self.found = true;
        }
        syn::visit::visit_expr_binary(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        // Slice-wise comparisons: `data.starts_with(&Pool::DISCRIMINATOR)`.
        let method = node.method.to_string();
        if matches!(
            method.as_str(),
            "starts_with" | "eq" | "ne" | "cmp" | "contains" | "eq_ignore_ascii_case"
        ) && (expr_reads_type_tag(&node.receiver) || node.args.iter().any(expr_reads_type_tag))
        {
            self.found = true;
        }
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_match(&mut self, node: &'ast syn::ExprMatch) {
        // `match header.account_type { ... }` dispatches on the tag.
        if expr_reads_type_tag(&node.expr) {
            self.found = true;
        }
        syn::visit::visit_expr_match(self, node);
    }

    fn visit_expr_try(&mut self, node: &'ast syn::ExprTry) {
        // `verify_tag(data, Pool::DISCRIMINATOR)?` -- a fallible call handed the
        // expected tag, whose failure propagates before deserialization. The
        // comparison itself may live in a callee we cannot resolve, but the tag
        // is demonstrably the value being checked.
        match peel(&node.expr) {
            Expr::Call(call) if call.args.iter().any(expr_reads_type_tag) => self.found = true,
            Expr::MethodCall(call) if call.args.iter().any(expr_reads_type_tag) => {
                self.found = true
            }
            _ => {}
        }
        syn::visit::visit_expr_try(self, node);
    }

    fn visit_expr_macro(&mut self, node: &'ast syn::ExprMacro) {
        if macro_asserts_type_tag(&node.mac) {
            self.found = true;
        }
        syn::visit::visit_expr_macro(self, node);
    }

    fn visit_stmt_macro(&mut self, node: &'ast syn::StmtMacro) {
        if macro_asserts_type_tag(&node.mac) {
            self.found = true;
        }
        syn::visit::visit_stmt_macro(self, node);
    }
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

    // --- REGRESSION GUARD (false negative): an init-flag check is not a type
    // check. `Vault` and `UserProfile` have identical wire layouts and both are
    // owned by the program, so a helper that validates owner + length + the
    // init byte lets an attacker pass a `UserProfile` where a `Vault` is
    // expected. The helper only *mentions* `is_initialized`; it never compares
    // an account-type tag. This MUST still flag.
    #[test]
    fn test_still_flags_init_only_helper_without_type_check() {
        let source = r#"
            fn validate_vault_account(info: &AccountInfo, program_id: &Pubkey) -> ProgramResult {
                if info.owner != program_id {
                    return Err(ProgramError::IllegalOwner);
                }
                let data = info.data.borrow();
                if data.len() < VAULT_LEN {
                    return Err(ProgramError::AccountDataTooSmall);
                }
                let is_initialized = data[0] != 0;
                if !is_initialized {
                    return Err(ProgramError::UninitializedAccount);
                }
                Ok(())
            }

            pub fn withdraw_from_vault(
                program_id: &Pubkey,
                accounts: &[AccountInfo],
                amount: u64,
            ) -> ProgramResult {
                let vault_info = &accounts[0];
                validate_vault_account(vault_info, program_id)?;
                let vault = Vault::try_from_slice(&vault_info.data.borrow())?;
                if amount > vault.amount {
                    return Err(ProgramError::InsufficientFunds);
                }
                **vault_info.try_borrow_mut_lamports()? -= amount;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A helper checking owner/length/init but never the account TYPE must not suppress: \
             a byte-compatible account of another type still passes it"
        );
    }

    // Same vulnerability with the init check spelled inline rather than bound to
    // a local. Neither spelling is a type check; both must flag.
    #[test]
    fn test_still_flags_inline_init_check_without_type_check() {
        let source = r#"
            fn validate_vault_account(info: &AccountInfo, program_id: &Pubkey) -> ProgramResult {
                if info.owner != program_id {
                    return Err(ProgramError::IllegalOwner);
                }
                let data = info.data.borrow();
                if data[0] == 0 {
                    return Err(ProgramError::UninitializedAccount);
                }
                Ok(())
            }

            pub fn withdraw_from_vault(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
                let vault_info = &accounts[0];
                validate_vault_account(vault_info, program_id)?;
                let vault = Vault::try_from_slice(&vault_info.data.borrow())?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "An inline init-flag check is not an account-type check and must not suppress"
        );
    }

    // The tag vocabulary must be *used*, not merely mentioned: a helper that
    // names a discriminator in a log line performs no check at all.
    #[test]
    fn test_still_flags_discriminator_only_mentioned_in_log() {
        let source = r#"
            fn note_load(info: &AccountInfo) {
                msg!("loading account, discriminator not verified");
            }

            fn load_pool(info: &AccountInfo) -> Result<Pool, ProgramError> {
                note_load(info);
                Pool::try_from_slice(&info.data.borrow()).map_err(|_| ProgramError::InvalidAccountData)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Mentioning 'discriminator' in a log string is not a discriminator check"
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
