use quote::ToTokens;
use syn::visit::Visit;
use syn::{FnArg, ItemFn};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;
use crate::utils::call_graph::{self, CheckKind};

pub struct MissingSignerDetector;

impl Detector for MissingSignerDetector {
    fn id(&self) -> &'static str {
        "SOL-001"
    }
    fn name(&self) -> &'static str {
        "missing-signer-check"
    }
    fn description(&self) -> &'static str {
        "Detects functions accepting AccountInfo without verifying is_signer"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Skip framework/library source — signer checks are architectural,
        // not per-function, in SPL and Anchor internals
        let file_str = ctx.file_path.to_string_lossy();
        if file_str.contains("/spl-token")
            || file_str.contains("/spl_token")
            || file_str.contains("/anchor-lang/")
            || file_str.contains("/anchor_lang/")
            || file_str.contains("/anchor-spl/")
            || file_str.contains("/anchor_spl/")
            || file_str.contains("/solana-program/")
            || file_str.contains("/solana_program/")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = SignerVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct SignerVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for SignerVisitor<'a> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions
        if fn_name.starts_with("test_") || has_attribute(&func.attrs, "test") {
            return;
        }

        // Skip internal helper functions — signer check typically at caller level
        if fn_name.starts_with('_')
            || fn_name.starts_with("inner_")
            || fn_name.starts_with("do_")
            || fn_name.starts_with("impl_")
            || fn_name.starts_with("handle_")
        {
            return;
        }

        // Skip SPL-style sub-processor functions called from process_instruction
        // These are dispatched from a main entry point that already validates the signer
        let fn_lower = fn_name.to_lowercase();
        if (fn_lower.starts_with("process_") && fn_lower != "process_instruction")
            || fn_lower.starts_with("execute_")
            || fn_lower.starts_with("_process_")
        {
            return;
        }

        // Skip CPI wrapper/helper functions — these forward authority through
        // invoke/invoke_signed; the caller is responsible for signer validation
        if matches!(
            fn_lower.as_str(),
            "transfer"
                | "burn"
                | "mint_to"
                | "freeze"
                | "thaw"
                | "approve"
                | "revoke"
                | "close"
                | "close_account"
                | "set_authority"
                | "create_account"
                | "create_new_account"
                | "create_or_allocate_account_raw"
                | "topup"
                | "dispose_account"
                | "extend_account_size"
                | "set_program_upgrade_authority"
        ) {
            return;
        }

        // Skip functions with CPI wrapper naming patterns
        if fn_lower.starts_with("transfer_")
            || fn_lower.starts_with("burn_")
            || fn_lower.starts_with("mint_")
            || fn_lower.starts_with("create_")
            || fn_lower.starts_with("close_")
            || fn_lower.starts_with("set_")
            || fn_lower.ends_with("_tokens")
            || fn_lower.ends_with("_account")
            || fn_lower.ends_with("_fees")
        {
            return;
        }

        // Skip utility/library functions that aren't entry points
        let fn_lower = fn_name.to_lowercase();
        if fn_lower.contains("serialize")
            || fn_lower.contains("deserialize")
            || fn_lower.contains("pack")
            || fn_lower.contains("unpack")
            || fn_lower.contains("parse")
            || fn_lower.contains("validate")
            || fn_lower.contains("verify")
            || fn_lower.contains("check")
            || fn_lower.contains("from_account")
            || fn_lower.contains("to_account")
        {
            return;
        }

        let body_src = fn_body_source(func);
        // Token-stream body with string-literal contents removed, so that words
        // appearing only inside `msg!("...")` / error strings cannot be mistaken
        // for real code (guards against FP idx 4).
        let clean_body = strip_string_literals(&body_src);

        // Skip if this uses Anchor's Signer<'info> or Account<'info, T> patterns
        let fn_src = func.to_token_stream().to_string();
        if fn_src.contains("Signer") || fn_src.contains("Context <") || fn_src.contains("Context<")
        {
            return;
        }

        // Look for AccountInfo parameters
        let mut unchecked_params: Vec<String> = Vec::new();

        for arg in &func.sig.inputs {
            if let FnArg::Typed(pat_type) = arg {
                let type_str = pat_type.ty.to_token_stream().to_string();
                if type_str.contains("AccountInfo") {
                    // Skip slice types like &[AccountInfo] - these are
                    // the standard process_instruction array parameter,
                    // not individual account references
                    if type_str.contains('[') || type_str.contains("Vec") {
                        continue;
                    }

                    // Get the parameter name
                    let param_name = pat_type.pat.to_token_stream().to_string();

                    // Skip common non-signer parameter names (iterators, program ids, sysvars)
                    let param_lower = param_name.to_lowercase();
                    if param_lower.contains("program")
                        || param_lower.contains("system")
                        || param_lower.contains("rent")
                        || param_lower.contains("clock")
                        || param_lower.contains("token")
                        || param_lower.contains("mint")
                        || param_lower.contains("metadata")
                        || param_lower.contains("associated")
                        || param_lower.contains("sysvar")
                        || param_lower.contains("pda")
                        || param_lower.contains("vault")
                        || param_lower.contains("pool")
                        || param_lower.contains("config")
                        || param_lower.contains("state")
                        || param_lower.contains("data")
                        || param_lower.contains("dest")
                        || param_lower.contains("source")
                    {
                        continue;
                    }

                    unchecked_params.push(param_name);
                }
            }
        }

        if unchecked_params.is_empty() {
            return;
        }

        // Check if body verifies the signer. Beyond the literal `is_signer`
        // property, this recognises other equivalent, documented enforcement
        // idioms so they are not falsely flagged:
        //   * `signer_key()` — solana_program API that returns Some(&Pubkey)
        //     iff is_signer is true (FP idx 2).
        //   * calls to a check helper named like assert_signer / require_signer /
        //     validate_signer (Metaplex `mpl_utils::assert_signer` etc.). Such a
        //     helper verifies the signer by construction; `?` aborts before any
        //     mutation (FP idx 0).
        //   * calls to a same-file helper whose body the call graph has resolved
        //     to actually contain an is_signer/has_signer check (FP idx 0, the
        //     `validate_authority(acct)?` case). This is a *resolved* delegation,
        //     not a name-based skip.
        let has_signer_check = body_src.contains("is_signer")
            || body_src.contains("has_signer")
            || clean_body.contains("signer_key")
            || body_calls_signer_assert_helper(&clean_body)
            || callee_checks_signer(&self.ctx.call_graph, &fn_name);

        // Check if the function does any state mutations.
        // Notes:
        //   * lamports() alone is a read-only getter; only borrow_mut on lamports
        //     is a mutation.
        //   * `deserialize` is a read, but naively substring-matches "serialize";
        //     strip it before testing so pure Borsh reads aren't treated as
        //     writes (FP idx 1).
        //   * has_mutations is computed on the string-literal-stripped body so
        //     that "invoke"/"serialize" inside a log message don't count
        //     (FP idx 4).
        let body_no_deser = clean_body.replace("deserialize", " ");
        let has_mutations = body_no_deser.contains("serialize")
            || clean_body.contains("try_borrow_mut")
            || clean_body.contains("borrow_mut")
            || clean_body.contains("invoke");

        // Check if any caller already checks signer before dispatching to this
        // function. Free-function callers are covered by the call graph;
        // impl-method callers (the SPL `impl Processor` dispatcher idiom) are not
        // tracked by build_call_graph, so resolve them directly here (FP idx 3).
        if !has_signer_check
            && (call_graph::caller_has_check(
                &self.ctx.call_graph,
                &fn_name,
                CheckKind::SignerCheck,
            ) || impl_method_caller_checks_signer(&self.ctx.ast, &fn_name))
        {
            return;
        }

        // Emit a single finding per function (not per param) to avoid noise
        if !has_signer_check && has_mutations {
            let line = span_to_line(&func.sig.ident.span());
            let params_str = if unchecked_params.len() == 1 {
                format!("'{}'", unchecked_params[0])
            } else {
                unchecked_params
                    .iter()
                    .map(|p| format!("'{}'", p))
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            self.findings.push(Finding {
                detector_id: "SOL-001".to_string(),
                name: "missing-signer-check".to_string(),
                severity: Severity::Critical,
                confidence: Confidence::High,
                message: format!(
                    "Function '{}' accepts AccountInfo {} without verifying is_signer",
                    func.sig.ident, params_str
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Add `if !account.is_signer { return Err(...) }` check, or use Anchor's `Signer<'info>` type".to_string(),
                chain: Chain::Solana,
            });
        }
        // Don't recurse into nested functions
    }
}

/// Remove the contents of double-quoted string literals from a token-stream
/// string, replacing each literal with a single space. This prevents words that
/// appear only inside `msg!("...")` or error-message strings from being matched
/// as if they were real code (mutation keywords, `is_signer`, etc.).
fn strip_string_literals(src: &str) -> String {
    let mut out = String::with_capacity(src.len());
    let mut in_str = false;
    let mut escaped = false;
    for c in src.chars() {
        if in_str {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
                out.push(' ');
            }
            // characters inside the string literal are dropped
        } else if c == '"' {
            in_str = true;
        } else {
            out.push(c);
        }
    }
    out
}

/// Returns true if the (string-literal-stripped) body calls a signer-assertion
/// helper such as `assert_signer`, `require_signer`, `validate_signer`,
/// `check_is_signer`, etc. These snake_case helper names verify signer status by
/// construction (e.g. Metaplex `mpl_utils::assert_signer`, whose body is
/// `if !info.is_signer { return Err(MissingRequiredSignature) }`), so the `?`
/// propagation of their result aborts the function before any mutation.
///
/// Only snake_case `verb_signer` / `verb_is_signer` identifier forms are matched,
/// so PascalCase items like an error variant `SignerCheckMissing` do NOT match —
/// avoiding accidental suppression of a real finding.
fn body_calls_signer_assert_helper(body: &str) -> bool {
    const VERBS: [&str; 6] = [
        "assert", "require", "check", "verify", "validate", "ensure",
    ];
    for v in VERBS {
        if body.contains(&format!("{}_signer", v)) || body.contains(&format!("{}_is_signer", v)) {
            return true;
        }
    }
    false
}

/// Returns true if any function called directly from `fn_name`'s body is a
/// same-file helper whose body the call graph resolved to contain a signer
/// check (is_signer / has_signer). This is a *resolved* delegation: it only
/// suppresses when the callee's body actually performs the check, never based on
/// name alone.
fn callee_checks_signer(graph: &call_graph::CallGraph, fn_name: &str) -> bool {
    if let Some(info) = graph.get(fn_name) {
        for callee in &info.calls {
            if let Some(callee_info) = graph.get(callee) {
                if callee_info.has_signer_check {
                    return true;
                }
            }
        }
    }
    false
}

/// Resolve impl-method callers that build_call_graph does not track. Returns
/// true if some method in an `impl` block both performs a signer check and calls
/// `target_fn` — the SPL `impl Processor { fn process(..) { check; dispatch(..) } }`
/// idiom, semantically identical to the free-function caller-validates pattern
/// the detector already accepts.
fn impl_method_caller_checks_signer(ast: &syn::File, target_fn: &str) -> bool {
    struct Finder<'a> {
        target_fn: &'a str,
        found: bool,
    }
    impl<'ast, 'a> Visit<'ast> for Finder<'a> {
        fn visit_impl_item_fn(&mut self, m: &'ast syn::ImplItemFn) {
            if self.found {
                return;
            }
            let body = m.block.to_token_stream().to_string();
            let clean = strip_string_literals(&body);
            let has_check = clean.contains("is_signer")
                || clean.contains("has_signer")
                || clean.contains("signer_key")
                || body_calls_signer_assert_helper(&clean);
            if has_check {
                let mut collector = CallNameCollector { names: Vec::new() };
                collector.visit_block(&m.block);
                if collector.names.iter().any(|n| n == self.target_fn) {
                    self.found = true;
                    return;
                }
            }
            syn::visit::visit_impl_item_fn(self, m);
        }
    }

    let mut finder = Finder {
        target_fn,
        found: false,
    };
    finder.visit_file(ast);
    finder.found
}

/// Collects the names of functions/methods called within a block.
struct CallNameCollector {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for CallNameCollector {
    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if let syn::Expr::Path(syn::ExprPath { path, .. }) = node.func.as_ref() {
            if let Some(seg) = path.segments.last() {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn run_detector(source: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let graph = crate::utils::call_graph::build_call_graph(&ast);
        let ctx = ScanContext::new(
            std::path::PathBuf::from("test.rs"),
            source.to_string(),
            ast,
            Chain::Solana,
            graph,
        );
        MissingSignerDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_signer() {
        let source = r#"
            fn withdraw_funds(account: &AccountInfo, recipient: &AccountInfo) {
                let mut data = account.try_borrow_mut_data().unwrap();
                data.serialize(&mut *dest.try_borrow_mut_data().unwrap()).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing signer check");
        assert_eq!(findings[0].detector_id, "SOL-001");
    }

    #[test]
    fn test_no_finding_process_subhandler() {
        let source = r#"
            fn process_transfer(account: &AccountInfo, dest: &AccountInfo) {
                let mut data = account.try_borrow_mut_data().unwrap();
                data.serialize(&mut *dest.try_borrow_mut_data().unwrap()).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag process_* sub-handler functions"
        );
    }

    #[test]
    fn test_no_finding_with_signer_check() {
        let source = r#"
            fn withdraw_funds(account: &AccountInfo, dest: &AccountInfo) {
                if !account.is_signer {
                    return Err(ProgramError::MissingRequiredSignature);
                }
                let mut data = account.try_borrow_mut_data().unwrap();
                data.serialize(&mut *dest.try_borrow_mut_data().unwrap()).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when is_signer is checked"
        );
    }

    #[test]
    fn test_no_finding_account_info_slice() {
        let source = r#"
            fn process_instruction(program_id: &Pubkey, accounts: &[AccountInfo], data: &[u8]) -> ProgramResult {
                let account_iter = &mut accounts.iter();
                let src = next_account_info(account_iter)?;
                invoke(&ix, accounts)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag &[AccountInfo] slice parameter"
        );
    }

    #[test]
    fn test_no_finding_anchor_signer() {
        let source = r#"
            fn process_transfer(ctx: Context<Transfer>) {
                let data = ctx.accounts.from.try_borrow_mut_data().unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag Anchor Context pattern"
        );
    }

    #[test]
    fn test_no_finding_internal_helper() {
        let source = r#"
            fn _transfer_tokens(account: &AccountInfo, dest: &AccountInfo) {
                let mut data = account.try_borrow_mut_data().unwrap();
                data.serialize(&mut *dest.try_borrow_mut_data().unwrap()).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag internal helper functions (prefixed with _)"
        );
    }

    #[test]
    fn test_no_finding_caller_checks_signer() {
        let source = r#"
            fn process_instruction(account: &AccountInfo, recipient: &AccountInfo) {
                if !account.is_signer {
                    return Err(ProgramError::MissingRequiredSignature);
                }
                withdraw_funds(account, recipient);
            }

            fn withdraw_funds(account: &AccountInfo, recipient: &AccountInfo) {
                let mut data = account.try_borrow_mut_data().unwrap();
                data.serialize(&mut *recipient.try_borrow_mut_data().unwrap()).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when caller checks signer (call graph analysis)"
        );
    }

    #[test]
    fn test_no_finding_utility_function() {
        let source = r#"
            fn validate_account(account: &AccountInfo) {
                let data = account.try_borrow_mut_data().unwrap();
                data.serialize(&mut buf).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag validate/verify/check utility functions"
        );
    }

    // ---- FP-elimination regression tests ----

    // FP idx 0: signer check delegated to a well-known assertion helper
    // (`mpl_utils::assert_signer`). The `?` aborts before any lamport mutation.
    #[test]
    fn test_no_finding_assert_signer_helper() {
        let source = r#"
            pub fn withdraw(authority: &AccountInfo, escrow_wallet: &AccountInfo, amount: u64) -> ProgramResult {
                assert_signer(authority)?;
                **escrow_wallet.try_borrow_mut_lamports()? -= amount;
                **authority.try_borrow_mut_lamports()? += amount;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a signer-assertion helper (assert_signer) is called"
        );
    }

    // FP idx 0 (resolved-delegation variant): the signer check lives in a
    // same-file helper whose body the call graph resolves to contain is_signer.
    #[test]
    fn test_no_finding_signer_check_delegated_to_local_helper() {
        let source = r#"
            pub fn withdraw(authority: &AccountInfo, escrow: &AccountInfo, amount: u64) -> ProgramResult {
                validate_authority(authority)?;
                **escrow.try_borrow_mut_lamports()? -= amount;
                Ok(())
            }

            fn validate_authority(authority: &AccountInfo) -> ProgramResult {
                if !authority.is_signer {
                    return Err(ProgramError::MissingRequiredSignature);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a resolved local helper performs the is_signer check"
        );
    }

    // FP idx 1: read-only getter mis-flagged because contains("serialize")
    // substring-matches "deserialize".
    #[test]
    fn test_no_finding_readonly_deserialize_getter() {
        let source = r#"
            pub fn get_balance(owner: &AccountInfo) -> Result<u64, ProgramError> {
                let state = TokenState::deserialize(&mut &owner.data.borrow()[..])?;
                Ok(state.balance)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a pure read that only deserializes account data"
        );
    }

    // FP idx 2: signer verified via AccountInfo::signer_key() instead of is_signer.
    #[test]
    fn test_no_finding_signer_key_check() {
        let source = r#"
            pub fn withdraw(authority: &AccountInfo, escrow: &AccountInfo, amount: u64) -> ProgramResult {
                let _key = authority
                    .signer_key()
                    .ok_or(ProgramError::MissingRequiredSignature)?;
                **escrow.try_borrow_mut_lamports()? -= amount;
                **authority.try_borrow_mut_lamports()? += amount;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the signer is enforced via signer_key()"
        );
    }

    // FP idx 3: caller signer check lives in an `impl Processor` block, which
    // build_call_graph does not track. The dispatched free fn must not be flagged.
    #[test]
    fn test_no_finding_impl_block_caller_checks_signer() {
        let source = r#"
            pub struct Processor;
            impl Processor {
                pub fn process(accounts: &[AccountInfo], amount: u64) -> ProgramResult {
                    let authority = &accounts[0];
                    if !authority.is_signer {
                        return Err(ProgramError::MissingRequiredSignature);
                    }
                    withdraw(authority, &accounts[1], amount)
                }
            }

            fn withdraw(authority: &AccountInfo, escrow: &AccountInfo, amount: u64) -> ProgramResult {
                **escrow.try_borrow_mut_lamports()? -= amount;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when an impl-block caller checks signer before dispatch"
        );
    }

    // FP idx 4: read-only logging function mis-flagged because "invoke"/"serialize"
    // appear only inside a msg! string literal.
    #[test]
    fn test_no_finding_log_only_string_literal_keywords() {
        let source = r#"
            pub fn log_status(user: &AccountInfo) {
                msg!("invoke count for {}: pending serialize", user.key);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a log-only fn whose 'invoke'/'serialize' are in a string literal"
        );
    }
}
