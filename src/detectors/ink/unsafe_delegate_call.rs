use quote::ToTokens;
use std::collections::HashMap;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{Attribute, Block, Expr, FnArg, ImplItemFn, ItemMod, Local, Pat, Signature, Token};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnsafeDelegateCallDetector;

impl Detector for UnsafeDelegateCallDetector {
    fn id(&self) -> &'static str {
        "INK-009"
    }
    fn name(&self) -> &'static str {
        "ink-unsafe-delegate-call"
    }
    fn description(&self) -> &'static str {
        "Detects delegate_call with user-controlled code hash (arbitrary code execution)"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Ink
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        // Pre-compute a within-file summary of every impl method so we can
        // resolve, for a flagged private helper, whether ALL of its callers
        // validate the code hash before invoking it (FP: private delegate
        // helper guarded by its public caller).
        let summaries = build_method_summaries(&ctx.ast);
        let mut visitor = DelegateVisitor {
            findings: &mut findings,
            ctx,
            summaries: &summaries,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// A within-file summary of one impl method, used for caller-based reasoning.
struct MethodSummary {
    name: String,
    /// Whether this method's own body validates the code hash it handles.
    has_verification: bool,
    /// Names of methods invoked from this method's body.
    calls: Vec<String>,
}

/// Does the method carry an `#[ink(message)]` attribute (i.e. is it an
/// externally dispatchable entry point)?
fn is_ink_message(attrs: &[Attribute]) -> bool {
    has_nested_attribute(attrs, "ink", "message")
}

/// Is this a `#[cfg(test)]` gated item?
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if let Some(ident) = attr.path().get_ident() {
            if ident == "cfg" {
                return attr.meta.to_token_stream().to_string().contains("test");
            }
        }
        false
    })
}

/// Is this a test function (`#[test]`, `#[ink::test]`, `#[tokio::test]`)?
fn is_test_fn(attrs: &[Attribute]) -> bool {
    has_attribute(attrs, "test")
        || has_attribute(attrs, "ink::test")
        || has_attribute(attrs, "tokio::test")
        || has_attribute(attrs, "async_std::test")
}

/// Collect the identifiers of parameters whose type or name indicates they
/// carry a code hash (`Hash`, `[u8; 32]`, or a name containing `hash`).
/// Deliberately does NOT treat a bare `target` parameter as a hash — that
/// matched governance vote-delegation params (`target: AccountId`).
fn collect_hash_params(sig: &Signature) -> Vec<String> {
    let mut params = Vec::new();
    for input in &sig.inputs {
        if let FnArg::Typed(pt) = input {
            let name = match pt.pat.as_ref() {
                Pat::Ident(pi) => pi.ident.to_string(),
                _ => continue,
            };
            let ty = pt.ty.to_token_stream().to_string();
            if ty.contains("Hash")
                || ty.contains("[u8 ; 32]")
                || ty.contains("[u8; 32]")
                || name.contains("hash")
                || name.contains("code_hash")
            {
                params.push(name);
            }
        }
    }
    params
}

/// Walk a method body and collect (a) whether an actual delegate-call
/// construct is present and (b) the rendered token strings of the arguments
/// passed to `.delegate(...)` / `.delegate_call(...)`.
fn analyze_delegate(block: &Block, body_src: &str) -> (bool, Vec<String>) {
    let mut mc = MethodCallCollector { calls: Vec::new() };
    mc.visit_block(block);

    let mut has_method_delegate = false;
    let mut args: Vec<String> = Vec::new();
    for call in &mc.calls {
        let m = call.method.to_string();
        if m == "delegate" || m == "delegate_call" {
            has_method_delegate = true;
            for a in &call.args {
                args.push(a.to_token_stream().to_string());
            }
        }
    }

    // Text fallback covers `DelegateCall::new(..)` / `Call::DelegateCall`
    // style constructs that are not a `.delegate(..)` method call.
    let has_delegate = has_method_delegate
        || body_src.contains("DelegateCall")
        || body_src.contains("delegate_call");

    (has_delegate, args)
}

/// Is the delegate target expression clearly trusted (contract storage set by
/// the contract itself, or a compile-time constant/literal) rather than a
/// value flowing in from a caller-supplied parameter?
fn arg_is_trusted(arg_tokens: &str) -> bool {
    let t = arg_tokens.trim();
    if t.is_empty() {
        return false;
    }
    // Storage field access: `self . x`, `& self . x`, `Self :: X`.
    if t.starts_with("self .") || t.starts_with("& self") || t.starts_with("Self ::") {
        return true;
    }
    // Getter on self: `self . approved_hash ()`.
    if t.starts_with("self.") {
        return true;
    }
    // SCREAMING_SNAKE_CASE constant (optionally path-qualified).
    let last = t.rsplit("::").next().unwrap_or(t).trim();
    if !last.is_empty()
        && last
            .chars()
            .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
    {
        return true;
    }
    // Literal.
    let first = t.chars().next().unwrap();
    if first == '"' || first == '\'' || first.is_ascii_digit() {
        return true;
    }
    false
}

/// Collect every `let` binding in a body as `name -> initializer tokens`, so a
/// comparison against a local can be resolved back to what the local actually
/// holds (`let zero = Hash::from([0u8; 32]);` is a sentinel, not an allow-list).
struct LetCollector {
    bindings: HashMap<String, String>,
}

impl<'ast> Visit<'ast> for LetCollector {
    fn visit_local(&mut self, l: &'ast Local) {
        let pat = match &l.pat {
            Pat::Type(pt) => pt.pat.as_ref(),
            other => other,
        };
        if let Pat::Ident(pi) = pat {
            if let Some(init) = &l.init {
                self.bindings.insert(
                    pi.ident.to_string(),
                    init.expr.to_token_stream().to_string(),
                );
            }
        }
        syn::visit::visit_local(self, l);
    }
}

/// Peel references / derefs / parens off an expression and render what is left.
fn core_tokens(e: &Expr) -> String {
    match e {
        Expr::Reference(r) => core_tokens(&r.expr),
        Expr::Paren(p) => core_tokens(&p.expr),
        Expr::Group(g) => core_tokens(&g.expr),
        Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => core_tokens(&u.expr),
        _ => e.to_token_stream().to_string(),
    }
}

/// Is this expression the hash parameter itself (possibly `.clone()`d)?
fn expr_is_hash_param(e: &Expr, hash_params: &[String]) -> bool {
    let t = core_tokens(e);
    let t = t.trim();
    hash_params
        .iter()
        .any(|p| t == p.as_str() || t.starts_with(&format!("{} .", p)))
}

/// Is this expression an *authoritative* source to check a code hash against —
/// contract storage (`self.approved_code_hash`), an associated item
/// (`Self::ALLOWED`), or a named constant (`KNOWN_HASH`)?
///
/// A locally constructed value is deliberately NOT authoritative: comparing a
/// code hash against `Hash::from([0u8; 32])` rejects exactly one hash out of
/// 2^256 and leaves every attacker-chosen hash accepted. That is a null check,
/// not a verification. Locals are resolved through their `let` initializer so
/// `let expected = KNOWN_HASH; ... == expected` still counts.
fn is_authoritative_source(tokens: &str, lets: &HashMap<String, String>, depth: usize) -> bool {
    let mut t = tokens.trim();
    while let Some(rest) = t.strip_prefix('&') {
        t = rest.trim();
    }
    if t.is_empty() {
        return false;
    }
    // Storage field / getter / associated item.
    if t.starts_with("self .") || t.starts_with("self.") || t.starts_with("Self ::") {
        return true;
    }
    // SCREAMING_SNAKE_CASE constant, optionally path-qualified. Requires at
    // least one letter so a bare `0` literal is not mistaken for a constant.
    let last = t.rsplit("::").next().unwrap_or(t).trim();
    if !last.is_empty()
        && last
            .chars()
            .all(|c| c.is_ascii_uppercase() || c == '_' || c.is_ascii_digit())
        && last.chars().any(|c| c.is_ascii_uppercase())
    {
        return true;
    }
    // A local binding: resolve once through its initializer.
    if depth > 0 {
        if let Some(init) = lets.get(t) {
            return is_authoritative_source(init, lets, depth - 1);
        }
    }
    false
}

/// Structural evidence that the body checks a hash parameter against an
/// authoritative source: an `==`/`!=` comparison, an `assert_eq!`/`assert_ne!`
/// over the pair, or a membership lookup (`contains`/`get`) on an allow-list
/// held in storage.
struct HashCheckFinder<'a> {
    hash_params: &'a [String],
    lets: &'a HashMap<String, String>,
    found: bool,
}

impl<'a> HashCheckFinder<'a> {
    /// One operand is the hash parameter, the other an authoritative source.
    fn is_checked_pair(&self, a: &Expr, b: &Expr) -> bool {
        let (at, bt) = (core_tokens(a), core_tokens(b));
        (expr_is_hash_param(a, self.hash_params) && is_authoritative_source(&bt, self.lets, 1))
            || (expr_is_hash_param(b, self.hash_params)
                && is_authoritative_source(&at, self.lets, 1))
    }

    fn check_macro(&mut self, mac: &syn::Macro) {
        let name = match mac.path.segments.last() {
            Some(s) => s.ident.to_string(),
            None => return,
        };
        if !matches!(
            name.as_str(),
            "assert_eq" | "assert_ne" | "debug_assert_eq" | "debug_assert_ne"
        ) {
            return;
        }
        if let Ok(args) = mac.parse_body_with(Punctuated::<Expr, Token![,]>::parse_terminated) {
            let args: Vec<Expr> = args.into_iter().collect();
            if args.len() >= 2 && self.is_checked_pair(&args[0], &args[1]) {
                self.found = true;
            }
        }
    }
}

impl<'ast, 'a> Visit<'ast> for HashCheckFinder<'a> {
    fn visit_expr_binary(&mut self, b: &'ast syn::ExprBinary) {
        if matches!(b.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_))
            && self.is_checked_pair(&b.left, &b.right)
        {
            self.found = true;
        }
        syn::visit::visit_expr_binary(self, b);
    }

    fn visit_expr_method_call(&mut self, c: &'ast syn::ExprMethodCall) {
        let m = c.method.to_string();
        if matches!(
            m.as_str(),
            "contains" | "contains_key" | "get" | "get_mut" | "contains_hash"
        ) && c
            .args
            .iter()
            .any(|a| expr_is_hash_param(a, self.hash_params))
            && is_authoritative_source(&core_tokens(&c.receiver), self.lets, 1)
        {
            self.found = true;
        }
        syn::visit::visit_expr_method_call(self, c);
    }

    fn visit_expr_macro(&mut self, m: &'ast syn::ExprMacro) {
        self.check_macro(&m.mac);
        syn::visit::visit_expr_macro(self, m);
    }

    fn visit_stmt_macro(&mut self, m: &'ast syn::StmtMacro) {
        self.check_macro(&m.mac);
        syn::visit::visit_stmt_macro(self, m);
    }
}

/// Does the body validate the code hash it delegates to? Recognises structural
/// checks of a hash parameter against an authoritative source, known allow-list
/// vocabulary, and caller/admin access gating (which means the hash is not
/// attacker-controlled).
fn body_has_hash_verification(block: &Block, body: &str, hash_params: &[String]) -> bool {
    // Explicit allow-list vocabulary.
    for kw in [
        "KNOWN_HASH",
        "ALLOWED_HASH",
        "whitelist",
        "allowed_hashes",
        "is_approved",
        "is_allowed",
        "is_whitelisted",
        "is_known_hash",
        "is_valid_hash",
        "approved_hashes",
        "approved_code_hash",
        "known_hashes",
        "allowed_code_hashes",
        "code_hash_whitelist",
    ] {
        if body.contains(kw) {
            return true;
        }
    }

    // Caller / admin / owner access gating: an untrusted caller can never
    // reach the delegate call, so the hash is not user-controlled.
    if body.contains("caller ()")
        && (body.contains(". admin")
            || body.contains(". owner")
            || body.contains("only_owner")
            || body.contains("ensure_owner")
            || body.contains("only_admin")
            || body.contains("ensure_admin")
            || body.contains("OwnerOnly")
            || body.contains("NotAuthorized")
            || body.contains("Unauthorized"))
    {
        return true;
    }

    // Per-parameter equality / membership guards. Structural, not textual: the
    // hash must actually be an operand of a comparison / assertion / allow-list
    // lookup whose OTHER side is an authoritative source. A textual `code_hash
    // ==` also matched `if code_hash == zero { return Err(..) }`, a null-sentinel
    // check that rejects one hash out of 2^256 and silenced the detector on a
    // fully attacker-controlled delegate target.
    if hash_params.is_empty() {
        return false;
    }
    let mut lc = LetCollector {
        bindings: HashMap::new(),
    };
    lc.visit_block(block);
    let mut finder = HashCheckFinder {
        hash_params,
        lets: &lc.bindings,
        found: false,
    };
    finder.visit_block(block);
    finder.found
}

/// Core decision: given a method, should it be reported as an unsafe
/// user-controlled delegate call?
fn method_is_unsafe_delegate(method: &ImplItemFn, summaries: &[MethodSummary]) -> bool {
    let body_src = method.block.to_token_stream().to_string();

    let (has_delegate, delegate_args) = analyze_delegate(&method.block, &body_src);
    if !has_delegate {
        return false;
    }

    // If every delegate target is trusted storage / a constant, no
    // caller-supplied parameter reaches the delegate call. This detector's
    // property (attacker-chosen code hash) cannot be violated.
    let target_trusted =
        !delegate_args.is_empty() && delegate_args.iter().all(|a| arg_is_trusted(a));
    if target_trusted {
        return false;
    }

    // Require an actual hash-carrying *parameter* (not a return type, not an
    // unrelated field). Without one, no user-controlled code hash exists.
    let hash_params = collect_hash_params(&method.sig);
    if hash_params.is_empty() {
        return false;
    }

    // The method itself validates the hash before delegating.
    if body_has_hash_verification(&method.block, &body_src, &hash_params) {
        return false;
    }

    // Private helper (not an #[ink(message)] entry point) whose every caller
    // validates the hash before invoking it: the hash can never be
    // user-controlled at the delegate site. Only trust this when we can
    // resolve callers within this file AND all of them validate.
    if !is_ink_message(&method.attrs) {
        let fn_name = method.sig.ident.to_string();
        let callers: Vec<&MethodSummary> = summaries
            .iter()
            .filter(|s| s.name != fn_name && s.calls.iter().any(|c| c == &fn_name))
            .collect();
        if !callers.is_empty() && callers.iter().all(|c| c.has_verification) {
            return false;
        }
    }

    true
}

/// Build a within-file summary for every impl method, skipping `#[cfg(test)]`
/// modules and test functions.
fn build_method_summaries(ast: &syn::File) -> Vec<MethodSummary> {
    struct SummaryBuilder {
        summaries: Vec<MethodSummary>,
    }
    impl<'ast> Visit<'ast> for SummaryBuilder {
        fn visit_item_mod(&mut self, m: &'ast ItemMod) {
            if is_cfg_test(&m.attrs) {
                return;
            }
            syn::visit::visit_item_mod(self, m);
        }
        fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
            if is_test_fn(&method.attrs) {
                return;
            }
            let body_src = method.block.to_token_stream().to_string();
            let hash_params = collect_hash_params(&method.sig);
            let has_verification =
                body_has_hash_verification(&method.block, &body_src, &hash_params);

            let mut mc = MethodCallCollector { calls: Vec::new() };
            mc.visit_block(&method.block);
            let calls = mc.calls.iter().map(|c| c.method.to_string()).collect();

            self.summaries.push(MethodSummary {
                name: method.sig.ident.to_string(),
                has_verification,
                calls,
            });
            syn::visit::visit_impl_item_fn(self, method);
        }
    }

    let mut b = SummaryBuilder {
        summaries: Vec::new(),
    };
    b.visit_file(ast);
    b.summaries
}

struct DelegateVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    summaries: &'a [MethodSummary],
}

impl<'ast, 'a> Visit<'ast> for DelegateVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Never analyze test-only code: `delegate` in a format string or a
        // mock is not a deployed vulnerability.
        if is_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        if is_test_fn(&method.attrs) {
            return;
        }

        if !method_is_unsafe_delegate(method, self.summaries) {
            syn::visit::visit_impl_item_fn(self, method);
            return;
        }

        let fn_name = method.sig.ident.to_string();
        let line = span_to_line(&method.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "INK-009".to_string(),
            name: "ink-unsafe-delegate-call".to_string(),
            severity: Severity::Critical,
            confidence: Confidence::High,
            message: format!(
                "Method '{}' performs delegate_call with user-controlled code hash",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&method.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Validate the code hash against a whitelist before delegate_call to prevent arbitrary code execution".to_string(),
            chain: Chain::Ink,
        });

        syn::visit::visit_impl_item_fn(self, method);
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
            Chain::Ink,
            std::collections::HashMap::new(),
        );
        UnsafeDelegateCallDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unsafe_delegate() {
        let source = r#"
            impl MyContract {
                pub fn proxy_call(&mut self, target_hash: Hash, input: Vec<u8>) {
                    ink::env::call::build_call::<Environment>()
                        .delegate(target_hash)
                        .exec_input(input)
                        .fire();
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect unsafe delegate call");
    }

    #[test]
    fn test_no_finding_with_verification() {
        let source = r#"
            impl MyContract {
                pub fn proxy_call(&mut self, target_hash: Hash, input: Vec<u8>) {
                    assert_eq!(target_hash, KNOWN_HASH);
                    ink::env::call::build_call::<Environment>()
                        .delegate(target_hash)
                        .fire();
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with hash verification"
        );
    }

    // FP 0: vote-delegation bookkeeping — no delegate_call, `delegated` field
    // and a `target: AccountId` param only.
    #[test]
    fn test_no_finding_vote_delegation() {
        let source = r#"
            impl Governance {
                #[ink(message)]
                pub fn delegate_votes(&mut self, target: AccountId, amount: Balance) {
                    let caller = self.env().caller();
                    self.delegated.insert((caller, target), &amount);
                    self.env().emit_event(Delegated { from: caller, to: target, amount });
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Vote-delegation bookkeeping has no delegate_call"
        );
    }

    // FP 1: properly guarded proxy using if/return Err instead of assert_eq!.
    #[test]
    fn test_no_finding_result_guarded_proxy() {
        let source = r#"
            impl Proxy {
                #[ink(message)]
                pub fn upgrade_and_call(&mut self, code_hash: Hash, input: Vec<u8>) -> Result<(), Error> {
                    if self.env().caller() != self.admin {
                        return Err(Error::NotAuthorized);
                    }
                    if code_hash != self.approved_code_hash {
                        return Err(Error::UnknownCodeHash);
                    }
                    ink::env::call::build_call::<Environment>()
                        .delegate(code_hash)
                        .exec_input(ExecutionInput::new(SELECTOR))
                        .invoke();
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Admin + hash-equality guarded proxy is safe"
        );
    }

    // FP 2: `Hash` only in the return type / an unrelated param, delegate
    // target is admin-set storage.
    #[test]
    fn test_no_finding_storage_delegate_target() {
        let source = r#"
            impl Proxy {
                #[ink(message)]
                pub fn forward(&mut self, input: Vec<u8>) -> Hash {
                    ink::env::call::build_call::<Environment>()
                        .delegate(self.logic_code_hash)
                        .exec_input(ExecutionInput::new(SELECTOR).push_arg(&input))
                        .invoke();
                    self.logic_code_hash
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Delegate target from self storage is not user-controlled"
        );
    }

    #[test]
    fn test_no_finding_unrelated_hash_param() {
        let source = r#"
            impl Proxy {
                #[ink(message)]
                pub fn forward(&mut self, doc_hash: Hash) -> Hash {
                    ink::env::call::build_call::<Environment>()
                        .delegate(self.logic_code_hash)
                        .invoke();
                    self.logic_code_hash
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Unrelated Hash param that never flows into delegate is safe"
        );
    }

    // FP 3: private delegate helper validated by its only (public) caller.
    #[test]
    fn test_no_finding_helper_validated_by_caller() {
        let source = r#"
            impl Proxy {
                fn do_delegate(&mut self, code_hash: Hash) {
                    ink::env::call::build_call::<Environment>()
                        .delegate(code_hash)
                        .invoke();
                }

                #[ink(message)]
                pub fn execute(&mut self, code_hash: Hash) -> Result<(), Error> {
                    if !self.allowed_hashes.contains(&code_hash) {
                        return Err(Error::BadHash);
                    }
                    self.do_delegate(code_hash);
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Private helper whose only caller validates the hash is safe"
        );
    }

    // FP 3 soundness guard: a private helper with an UNVALIDATED caller must
    // still be flagged (no false negative).
    #[test]
    fn test_flags_helper_with_unvalidated_caller() {
        let source = r#"
            impl Proxy {
                fn do_delegate(&mut self, code_hash: Hash) {
                    ink::env::call::build_call::<Environment>()
                        .delegate(code_hash)
                        .invoke();
                }

                #[ink(message)]
                pub fn execute(&mut self, code_hash: Hash) {
                    self.do_delegate(code_hash);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Helper reached by an unvalidated caller must still be flagged"
        );
    }

    // MUST STILL FLAG: a non-zero sanity check on the code hash is NOT a
    // verification. `code_hash == zero` rejects exactly one hash out of 2^256;
    // the attacker still passes their own uploaded code hash and gets arbitrary
    // code executed against this contract's storage. ADV-206's textual
    // `format!("{} ==", p)` guard silenced this genuinely vulnerable proxy.
    #[test]
    fn test_still_flags_zero_sentinel_hash_check() {
        let source = r#"
            impl UpgradeableProxy {
                #[ink(message)]
                pub fn execute(&mut self, code_hash: Hash, selector: [u8; 4]) -> Result<(), Error> {
                    let zero = Hash::from([0u8; 32]);
                    if code_hash == zero {
                        return Err(Error::ZeroCodeHash);
                    }

                    self.calls = self.calls.saturating_add(1);

                    build_call::<ink::env::DefaultEnvironment>()
                        .delegate(code_hash)
                        .exec_input(ExecutionInput::new(Selector::new(selector)))
                        .returns::<()>()
                        .try_invoke()
                        .map_err(|_| Error::DelegateFailed)?
                        .map_err(|_| Error::DelegateFailed)?;

                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A zero-sentinel check is not hash verification: the delegate target is \
             still fully attacker-controlled"
        );
    }

    // MUST STILL FLAG: same class as above via `Hash::default()`, and comparing
    // against a freshly decoded caller-supplied value is likewise no allow-list.
    #[test]
    fn test_still_flags_default_sentinel_hash_check() {
        let source = r#"
            impl Proxy {
                #[ink(message)]
                pub fn run(&mut self, code_hash: Hash) -> Result<(), Error> {
                    if code_hash != Hash::default() {
                        ink::env::call::build_call::<Environment>()
                            .delegate(code_hash)
                            .invoke();
                    }
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Comparing against Hash::default() is a null check, not verification"
        );
    }

    // The structural check must still accept a real allow-list comparison
    // against contract storage even when it is bound to a local first.
    #[test]
    fn test_no_finding_hash_compared_to_local_bound_storage() {
        let source = r#"
            impl Proxy {
                #[ink(message)]
                pub fn run(&mut self, code_hash: Hash) -> Result<(), Error> {
                    let expected = self.logic_hash;
                    if code_hash != expected {
                        return Err(Error::BadHash);
                    }
                    ink::env::call::build_call::<Environment>()
                        .delegate(code_hash)
                        .invoke();
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Comparison against storage via a local binding is real verification"
        );
    }

    // FP 4: test/mock code with `delegate` only inside a string literal.
    #[test]
    fn test_no_finding_test_module_string_literal() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                impl TestHarness {
                    fn record(&mut self, target: Hash) {
                        self.log.push(format!("delegate to {:?}", target));
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "cfg(test) mock with delegate in a string literal is not a vuln"
        );
    }
}
