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

        // Token-stream body with string-literal contents removed, so that words
        // appearing only inside `msg!("...")` / error strings cannot be mistaken
        // for real code (guards against FP idx 4).
        let clean_body = strip_string_literals(&fn_body_source(func));

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
        //
        // Every arm below is resolved from the AST rather than by a substring
        // scan of the body text: the signer property must be *touched* by real
        // code, and a helper must be *called* under its exact identifier. A body
        // that merely spells a signer-ish word — `validate_signer_seeds(..)`,
        // which only validates PDA seeds — enforces nothing and must not suppress.
        let has_signer_check = body_touches_signer_property(&func.block)
            || calls_signer_assert_helper(
                &func.block,
                &self.ctx.call_graph,
                Some(&unchecked_params),
            )
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
            ) || impl_method_caller_checks_signer(
                &self.ctx.ast,
                &self.ctx.call_graph,
                &fn_name,
            ))
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

/// The identifiers that name the signer property itself. Touching any of these
/// in real code is what actually reads signer status:
///   * `is_signer` / `has_signer` — the AccountInfo field.
///   * `signer_key` — solana_program getter returning Some(&Pubkey) iff signed.
const SIGNER_PROPERTY_IDENTS: [&str; 3] = ["is_signer", "has_signer", "signer_key"];

/// Returns true if `block` touches the signer property as *code*: a field access
/// (`authority.is_signer`), a method call (`authority.signer_key()`), a path
/// (`AccountInfo::is_signer(a)`), or an identifier inside a macro invocation
/// (`assert!(authority.is_signer)` — syn keeps macro bodies as opaque tokens, so
/// those are scanned at the token level, where an `Ident` is still a whole
/// identifier and string literals are `Literal`s that can never match).
///
/// This replaces a `body.contains("is_signer")` scan, which had neither
/// identifier boundaries nor any notion of use: it fired on `msg!("is_signer")`
/// and on unrelated identifiers that merely embed the word.
fn body_touches_signer_property(block: &syn::Block) -> bool {
    struct Finder {
        found: bool,
    }
    impl Finder {
        fn hit(&mut self, ident: &syn::Ident) {
            if SIGNER_PROPERTY_IDENTS.contains(&ident.to_string().as_str()) {
                self.found = true;
            }
        }
    }
    impl<'ast> Visit<'ast> for Finder {
        fn visit_expr_field(&mut self, node: &'ast syn::ExprField) {
            if let syn::Member::Named(ident) = &node.member {
                self.hit(ident);
            }
            syn::visit::visit_expr_field(self, node);
        }

        fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
            self.hit(&node.method);
            syn::visit::visit_expr_method_call(self, node);
        }

        fn visit_path(&mut self, node: &'ast syn::Path) {
            for seg in &node.segments {
                self.hit(&seg.ident);
            }
            syn::visit::visit_path(self, node);
        }

        fn visit_macro(&mut self, node: &'ast syn::Macro) {
            if tokens_contain_ident(node.tokens.clone(), &SIGNER_PROPERTY_IDENTS) {
                self.found = true;
            }
            syn::visit::visit_macro(self, node);
        }
    }

    let mut finder = Finder { found: false };
    finder.visit_block(block);
    finder.found
}

/// Recursively scan a token stream for any of `idents` as a whole `Ident` token.
/// Used for macro bodies, which syn does not parse into expressions.
fn tokens_contain_ident(tokens: proc_macro2::TokenStream, idents: &[&str]) -> bool {
    for tt in tokens {
        match tt {
            proc_macro2::TokenTree::Ident(i) => {
                if idents.contains(&i.to_string().as_str()) {
                    return true;
                }
            }
            proc_macro2::TokenTree::Group(g) => {
                if tokens_contain_ident(g.stream(), idents) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Returns true if `name` is *exactly* one of the signer-assertion helper forms
/// (`assert_signer`, `require_signer`, `validate_signer`, `check_is_signer`, …).
///
/// The comparison is an equality test on a whole call-site identifier, not a
/// substring test on body text. The old substring form had no trailing boundary,
/// so `validate_signer_seeds` — a PDA-seed check that performs no signer
/// verification whatsoever — matched `validate_signer` and silenced a real
/// finding.
fn is_signer_assert_helper_name(name: &str) -> bool {
    const VERBS: [&str; 6] = ["assert", "require", "check", "verify", "validate", "ensure"];
    VERBS
        .iter()
        .any(|v| name == format!("{}_signer", v) || name == format!("{}_is_signer", v))
}

/// A call resolved from the AST: the callee's final path segment, plus the token
/// text of the values the callee is applied to (receiver included for method
/// calls, raw tokens for macros).
struct CallSite {
    name: String,
    args: String,
}

/// Collects real call sites — plain calls, method calls and macro invocations —
/// from a block. Callee names come from AST identifiers, so `validate_signer`
/// and `validate_signer_seeds` are distinct callees, and a word inside a string
/// literal is never a callee.
struct CallSiteCollector {
    sites: Vec<CallSite>,
}

impl<'ast> Visit<'ast> for CallSiteCollector {
    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if let syn::Expr::Path(syn::ExprPath { path, .. }) = node.func.as_ref() {
            if let Some(seg) = path.segments.last() {
                self.sites.push(CallSite {
                    name: seg.ident.to_string(),
                    args: node
                        .args
                        .iter()
                        .map(|a| a.to_token_stream().to_string())
                        .collect::<Vec<_>>()
                        .join(" , "),
                });
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        // The receiver is the value the assertion is applied to for the
        // `authority.assert_signer()?` shape, so it counts as an argument.
        let mut args = node.receiver.to_token_stream().to_string();
        for a in &node.args {
            args.push_str(" , ");
            args.push_str(&a.to_token_stream().to_string());
        }
        self.sites.push(CallSite {
            name: node.method.to_string(),
            args,
        });
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_macro(&mut self, node: &'ast syn::Macro) {
        if let Some(seg) = node.path.segments.last() {
            self.sites.push(CallSite {
                name: seg.ident.to_string(),
                args: node.tokens.to_string(),
            });
        }
        syn::visit::visit_macro(self, node);
    }
}

/// Returns true if `block` calls a signer-assertion helper (Metaplex
/// `mpl_utils::assert_signer` and friends, whose body is
/// `if !info.is_signer { return Err(MissingRequiredSignature) }`, so that `?`
/// aborts before any mutation).
///
/// Three structural requirements replace the old substring test:
///   1. the helper must appear as an actual *call site* resolved from the AST,
///      matching a helper form under its exact identifier (see
///      `is_signer_assert_helper_name`);
///   2. if the helper is defined in this file, the call graph's resolved body
///      decides — a local helper that never reads signer status does not
///      suppress, however suggestively it is named. Only helpers whose body we
///      cannot see (external crates) are trusted on the name alone;
///   3. the assertion must be applied to one of `risky_params` — the very
///      accounts we would otherwise flag — so asserting on some unrelated value
///      does not clear an account that was never checked. Pass `None` to skip
///      this when there is no specific account at stake.
fn calls_signer_assert_helper(
    block: &syn::Block,
    graph: &call_graph::CallGraph,
    risky_params: Option<&[String]>,
) -> bool {
    let mut collector = CallSiteCollector { sites: Vec::new() };
    collector.visit_block(block);

    for site in &collector.sites {
        if !is_signer_assert_helper_name(&site.name) {
            continue;
        }
        // (2) A same-file definition overrides its own name.
        if let Some(info) = graph.get(&site.name) {
            if !info.has_signer_check {
                continue;
            }
        }
        // (3) The assertion must land on an account we would otherwise flag.
        match risky_params {
            Some(params) if !params.iter().any(|p| args_mention(&site.args, p)) => continue,
            _ => return true,
        }
    }
    false
}

/// Returns true if the token text `args` mentions `param` as a whole identifier,
/// so `escrow` does not match `escrow_wallet` (or vice versa). Token-stream text
/// is space-separated, but `&authority` / `authority.key` shapes mean the
/// boundary still has to be checked against the neighbouring characters.
fn args_mention(args: &str, param: &str) -> bool {
    if param.is_empty() {
        return false;
    }
    let is_ident_char = |c: char| c.is_alphanumeric() || c == '_';
    for (idx, _) in args.match_indices(param) {
        let before_ok = args[..idx]
            .chars()
            .next_back()
            .map_or(true, |c| !is_ident_char(c));
        let after_ok = args[idx + param.len()..]
            .chars()
            .next()
            .map_or(true, |c| !is_ident_char(c));
        if before_ok && after_ok {
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
fn impl_method_caller_checks_signer(
    ast: &syn::File,
    graph: &call_graph::CallGraph,
    target_fn: &str,
) -> bool {
    struct Finder<'a> {
        target_fn: &'a str,
        graph: &'a call_graph::CallGraph,
        found: bool,
    }
    impl<'ast, 'a> Visit<'ast> for Finder<'a> {
        fn visit_impl_item_fn(&mut self, m: &'ast syn::ImplItemFn) {
            if self.found {
                return;
            }
            // Resolved the same structural way as the primary guard. No specific
            // account is at stake here — the question is only whether this
            // dispatcher checks a signer at all — so no param binding is applied.
            let has_check = body_touches_signer_property(&m.block)
                || calls_signer_assert_helper(&m.block, self.graph, None);
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
        graph,
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

    // ---- MUST-STILL-FLAG regression tests ----
    // These pin recall. A future FP-reduction pass that trips one of them has
    // silenced a real vulnerability, not removed a false positive.

    // A helper named `validate_signer_seeds` validates PDA seeds and performs no
    // signer verification at all, but the ADV-206 guard substring-matched it
    // against `validate_signer` and suppressed the finding. `authority` is never
    // checked for is_signer, so any caller can name an arbitrary non-signing
    // authority and drain the escrow's lamports.
    #[test]
    fn test_still_flags_signer_named_helper_that_only_checks_seeds() {
        let source = r#"
            pub fn withdraw_all(authority: &AccountInfo, escrow: &AccountInfo, program_id: &Pubkey, bump: u8, amount: u64) -> ProgramResult {
                validate_signer_seeds(escrow, program_id, bump)?;
                **escrow.try_borrow_mut_lamports()? -= amount;
                **authority.try_borrow_mut_lamports()? += amount;
                Ok(())
            }

            fn validate_signer_seeds(escrow: &AccountInfo, program_id: &Pubkey, bump: u8) -> ProgramResult {
                let expected = Pubkey::create_program_address(&[b"escrow", &[bump]], program_id)
                    .map_err(|_| ProgramError::InvalidSeeds)?;
                if expected != *escrow.key {
                    return Err(ProgramError::InvalidSeeds);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Must flag: `validate_signer_seeds` checks PDA seeds, not is_signer"
        );
        assert_eq!(findings[0].detector_id, "SOL-001");
    }

    // Control for the test above: byte-identical vulnerability with the helper
    // renamed `validate_pda_seeds`. Same code, same vuln, evasion removed — both
    // must flag, and the pair proves the verdict no longer turns on the name.
    #[test]
    fn test_still_flags_pda_seeds_helper_control() {
        let source = r#"
            pub fn withdraw_all(authority: &AccountInfo, escrow: &AccountInfo, program_id: &Pubkey, bump: u8, amount: u64) -> ProgramResult {
                validate_pda_seeds(escrow, program_id, bump)?;
                **escrow.try_borrow_mut_lamports()? -= amount;
                **authority.try_borrow_mut_lamports()? += amount;
                Ok(())
            }

            fn validate_pda_seeds(escrow: &AccountInfo, program_id: &Pubkey, bump: u8) -> ProgramResult {
                let expected = Pubkey::create_program_address(&[b"escrow", &[bump]], program_id)
                    .map_err(|_| ProgramError::InvalidSeeds)?;
                if expected != *escrow.key {
                    return Err(ProgramError::InvalidSeeds);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Must flag: control for the validate_signer_seeds probe"
        );
    }

    // A local helper whose name matches a real assertion form exactly, but whose
    // resolved body only checks seeds. The name must not beat the body.
    #[test]
    fn test_still_flags_local_assert_signer_helper_that_checks_nothing() {
        let source = r#"
            pub fn withdraw_all(authority: &AccountInfo, escrow: &AccountInfo, amount: u64) -> ProgramResult {
                assert_signer(escrow)?;
                **escrow.try_borrow_mut_lamports()? -= amount;
                **authority.try_borrow_mut_lamports()? += amount;
                Ok(())
            }

            fn assert_signer(escrow: &AccountInfo) -> ProgramResult {
                if *escrow.key == Pubkey::default() {
                    return Err(ProgramError::InvalidSeeds);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Must flag: local assert_signer resolves to a body that never reads is_signer"
        );
    }

    // The word `is_signer` appearing only inside a log string is not a check.
    #[test]
    fn test_still_flags_is_signer_only_in_string_literal() {
        let source = r#"
            pub fn withdraw_all(authority: &AccountInfo, escrow: &AccountInfo, amount: u64) -> ProgramResult {
                msg!("skipping is_signer verification for speed");
                **escrow.try_borrow_mut_lamports()? -= amount;
                **authority.try_borrow_mut_lamports()? += amount;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Must flag: `is_signer` inside a msg! literal performs no verification"
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
