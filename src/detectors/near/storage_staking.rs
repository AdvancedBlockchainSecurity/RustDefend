use std::collections::{HashMap, HashSet};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{
    Attribute, Block, Expr, ExprCall, ExprIf, ExprMethodCall, ExprPath, ExprReturn, FnArg, ItemFn,
    ItemMod, Local, Macro, Pat, ReturnType, Signature, Stmt, Token,
};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct StorageStakingDetector;

impl Detector for StorageStakingDetector {
    fn id(&self) -> &'static str {
        "NEAR-003"
    }
    fn name(&self) -> &'static str {
        "storage-staking-auth"
    }
    fn description(&self) -> &'static str {
        "Detects storage_deposit/storage_withdraw without predecessor_account_id check"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Near
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Build a within-file summary of every (non-test) function/method: what it
        // actually *does* with the caller identity, and which callees it hands a
        // resolved identity to. This lets us soundly resolve whether the caller
        // identity is authorized one frame up (a trusted caller that reads
        // `predecessor_account_id` and passes the account down) or one frame down
        // (auth factored into a shared helper), instead of relying on a literal
        // match on a body — a body that merely *mentions* the token (logging the
        // caller into an event) authorizes nothing.
        let mut collector = FnDefCollector {
            roles: HashMap::new(),
            identity_args: HashMap::new(),
        };
        collector.visit_file(&ctx.ast);

        let mut findings = Vec::new();
        let mut visitor = StorageVisitor {
            findings: &mut findings,
            ctx,
            roles: &collector.roles,
            identity_args: &collector.identity_args,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Returns true if the `#[cfg(test)]` (or `#[cfg(all(test, ...))]`) attribute is
/// present. Contents of test modules are compiled out of the deployed wasm and
/// carry no on-chain authorization surface.
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if !attr.path().is_ident("cfg") {
            return false;
        }
        let tokens = attr.meta.to_token_stream().to_string();
        let compact: String = tokens.chars().filter(|c| !c.is_whitespace()).collect();
        compact.contains("(test)") || compact.contains("(test,") || compact.contains(",test)")
    })
}

/// Returns true if the function carries a test attribute (`#[test]`,
/// `#[tokio::test]`, `#[ink::test]`, ...). Such functions are harnesses, not
/// contract entry points.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    has_attribute(attrs, "test")
        || has_attribute(attrs, "tokio::test")
        || has_attribute(attrs, "ink::test")
        || has_attribute(attrs, "near::test")
        || has_attribute(attrs, "actix_rt::test")
        || has_attribute(attrs, "async_std::test")
}

/// Collect the names of every function/method invoked inside a block.
fn collect_callees_block(block: &Block) -> Vec<String> {
    let mut collector = CalleeCollector { calls: Vec::new() };
    collector.visit_block(block);
    collector.calls
}

/// True if the signature declares a parameter that carries an account identity
/// (named `account_id` or typed `AccountId`, including `&AccountId` /
/// `Option<AccountId>`). Such helpers receive an already-resolved identity from
/// their caller rather than needing to consult `predecessor_account_id`.
fn has_account_id_param(sig: &Signature) -> bool {
    sig.inputs.iter().any(|arg| {
        if let FnArg::Typed(pt) = arg {
            let ty = pt.ty.to_token_stream().to_string();
            let pat = pt.pat.to_token_stream().to_string();
            ty.contains("AccountId") || pat == "account_id"
        } else {
            false
        }
    })
}

/// True if the signature has a *required* (non-`Option`) `AccountId` parameter,
/// i.e. the beneficiary is always supplied by the caller and never defaulted
/// from `predecessor_account_id`. Under NEP-145 such a `storage_deposit` is
/// permissionless by design.
fn has_required_account_id_param(sig: &Signature) -> bool {
    sig.inputs.iter().any(|arg| {
        if let FnArg::Typed(pt) = arg {
            let ty = pt.ty.to_token_stream().to_string();
            ty.contains("AccountId") && !ty.contains("Option")
        } else {
            false
        }
    })
}

/// The leading arguments of an assertion macro that form the *decision*. Every
/// argument after them is the panic message, where a mention of the caller
/// proves nothing: `assert!(x, "rejected {}", env::predecessor_account_id())`
/// checks nothing whatsoever about the caller.
fn assert_condition_arity(name: &str) -> Option<usize> {
    match name {
        "assert" | "debug_assert" | "require" => Some(1),
        "assert_eq" | "assert_ne" | "debug_assert_eq" | "debug_assert_ne" | "require_eq" => Some(2),
        _ => None,
    }
}

/// The trailing segment of a macro's path (`near_sdk::require!` -> `require`).
fn macro_name(mac: &Macro) -> String {
    mac.path
        .segments
        .last()
        .map(|s| s.ident.to_string())
        .unwrap_or_default()
}

/// True if any identifier inside an opaque macro token tree satisfies `pred`.
fn tokens_mention(tokens: TokenStream, pred: &dyn Fn(&str) -> bool) -> bool {
    tokens.into_iter().any(|tt| match tt {
        TokenTree::Ident(id) => pred(&id.to_string()),
        TokenTree::Group(g) => tokens_mention(g.stream(), pred),
        _ => false,
    })
}

/// True if `ident` names the caller identity: the `predecessor_account_id` read
/// itself, or a local bound from one.
fn is_identity_ident(taint: &HashSet<String>, ident: &str) -> bool {
    ident == "predecessor_account_id" || taint.contains(ident)
}

/// Finds *reads* of the caller identity inside an expression tree.
struct PredecessorReadVisitor<'t> {
    taint: &'t HashSet<String>,
    found: bool,
}

impl<'ast, 't> Visit<'ast> for PredecessorReadVisitor<'t> {
    fn visit_expr_path(&mut self, node: &'ast ExprPath) {
        if let Some(segment) = node.path.segments.last() {
            if is_identity_ident(self.taint, &segment.ident.to_string()) {
                self.found = true;
            }
        }
        syn::visit::visit_expr_path(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        if is_identity_ident(self.taint, &node.method.to_string()) {
            self.found = true;
        }
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_macro(&mut self, node: &'ast Macro) {
        // Macro bodies are opaque token trees; fall back to an ident scan.
        let taint = self.taint;
        if tokens_mention(node.tokens.clone(), &|id| is_identity_ident(taint, id)) {
            self.found = true;
        }
    }
}

/// True if the expression reads the caller identity, directly or through a local
/// bound from one.
fn expr_reads_predecessor(expr: &Expr, taint: &HashSet<String>) -> bool {
    let mut visitor = PredecessorReadVisitor {
        taint,
        found: false,
    };
    visitor.visit_expr(expr);
    visitor.found
}

/// Collect the idents a `let` pattern binds (`let caller`, `let (a, b)`, ...).
fn collect_pat_idents(pat: &Pat, out: &mut HashSet<String>) {
    match pat {
        Pat::Ident(pi) => {
            out.insert(pi.ident.to_string());
        }
        Pat::Tuple(t) => t.elems.iter().for_each(|p| collect_pat_idents(p, out)),
        Pat::Type(pt) => collect_pat_idents(&pt.pat, out),
        Pat::Reference(pr) => collect_pat_idents(&pr.pat, out),
        _ => {}
    }
}

/// Records locals bound from a caller-identity read: after
/// `let caller = env::predecessor_account_id();`, `caller` *is* the caller.
struct TaintCollector {
    names: HashSet<String>,
}

impl<'ast> Visit<'ast> for TaintCollector {
    fn visit_local(&mut self, node: &'ast Local) {
        if let Some(init) = &node.init {
            if expr_reads_predecessor(&init.expr, &self.names) {
                collect_pat_idents(&node.pat, &mut self.names);
            }
        }
        syn::visit::visit_local(self, node);
    }
}

/// The locals in `block` that carry the caller identity, to a fixpoint so that
/// chained bindings (`let caller = env::predecessor_account_id(); let who =
/// caller;`) propagate.
fn predecessor_taint(block: &Block) -> HashSet<String> {
    let mut names = HashSet::new();
    loop {
        let mut collector = TaintCollector {
            names: names.clone(),
        };
        collector.visit_block(block);
        if collector.names.len() == names.len() {
            return names;
        }
        names = collector.names;
    }
}

/// Finds early rejection — a panic or an early return — inside a block.
struct RejectVisitor {
    found: bool,
}

impl<'ast> Visit<'ast> for RejectVisitor {
    fn visit_expr_return(&mut self, node: &'ast ExprReturn) {
        self.found = true;
        syn::visit::visit_expr_return(self, node);
    }

    fn visit_macro(&mut self, node: &'ast Macro) {
        if matches!(
            macro_name(node).as_str(),
            "panic" | "unreachable" | "assert" | "assert_eq" | "assert_ne" | "require"
        ) {
            self.found = true;
        }
    }

    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let Expr::Path(ExprPath { path, .. }) = node.func.as_ref() {
            if let Some(segment) = path.segments.last() {
                if matches!(
                    segment.ident.to_string().as_str(),
                    "panic_str" | "panic_utf8" | "abort"
                ) {
                    self.found = true;
                }
            }
        }
        syn::visit::visit_expr_call(self, node);
    }
}

/// True if the block rejects the call outright (panics or returns early). This
/// is what separates an authorization guard (`if caller != owner { panic!() }`)
/// from a branch that merely happens to read the caller.
fn block_rejects(block: &Block) -> bool {
    let mut visitor = RejectVisitor { found: false };
    visitor.visit_block(block);
    visitor.found
}

/// Finds the structural sites where the caller identity actually drives a
/// decision. Merely *mentioning* `predecessor_account_id` — logging it into an
/// event, formatting it into a panic message — authorizes nothing.
struct EnforcementVisitor<'t> {
    taint: &'t HashSet<String>,
    enforced: bool,
}

impl<'ast, 't> Visit<'ast> for EnforcementVisitor<'t> {
    fn visit_macro(&mut self, node: &'ast Macro) {
        // `assert!(caller == owner)` / `require!(self.is_member(&caller))`: only
        // the leading condition operands count, never the message arguments.
        if let Some(arity) = assert_condition_arity(&macro_name(node)) {
            if let Ok(args) = node.parse_body_with(Punctuated::<Expr, Token![,]>::parse_terminated)
            {
                if args
                    .iter()
                    .take(arity)
                    .any(|arg| expr_reads_predecessor(arg, self.taint))
                {
                    self.enforced = true;
                }
            }
        }
    }

    fn visit_expr_if(&mut self, node: &'ast ExprIf) {
        // `if caller != self.owner { env::panic_str("unauthorized") }`: branches
        // on the caller AND rejects.
        if expr_reads_predecessor(&node.cond, self.taint) && block_rejects(&node.then_branch) {
            self.enforced = true;
        }
        syn::visit::visit_expr_if(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        // `self.accounts.get(&caller).expect("not registered")`: the lookup is
        // keyed by the caller and aborts when the caller is absent.
        if matches!(node.method.to_string().as_str(), "expect" | "unwrap")
            && expr_reads_predecessor(&node.receiver, self.taint)
        {
            self.enforced = true;
        }
        syn::visit::visit_expr_method_call(self, node);
    }
}

/// Finds `return <caller identity>` in a helper body.
struct ReturnExprVisitor<'t> {
    taint: &'t HashSet<String>,
    found: bool,
}

impl<'ast, 't> Visit<'ast> for ReturnExprVisitor<'t> {
    fn visit_expr_return(&mut self, node: &'ast ExprReturn) {
        if let Some(expr) = &node.expr {
            if expr_reads_predecessor(expr, self.taint) {
                self.found = true;
            }
        }
        syn::visit::visit_expr_return(self, node);
    }
}

/// True if the helper hands the *resolved* caller identity back to its caller
/// (`fn caller(&self) -> AccountId { env::predecessor_account_id() }`). What it
/// returns is authoritative, exactly like an inline read. Restricted to
/// `AccountId`-shaped returns: a helper returning some other value merely
/// derived from the caller is not an identity resolution.
fn returns_caller_identity(sig: &Signature, block: &Block, taint: &HashSet<String>) -> bool {
    let ty = match &sig.output {
        ReturnType::Type(_, ty) => ty,
        ReturnType::Default => return false,
    };
    if !ty.to_token_stream().to_string().contains("AccountId") {
        return false;
    }
    if matches!(block.stmts.last(), Some(Stmt::Expr(expr, None)) if expr_reads_predecessor(expr, taint))
    {
        return true;
    }
    let mut visitor = ReturnExprVisitor {
        taint,
        found: false,
    };
    visitor.visit_block(block);
    visitor.found
}

/// What a same-file function actually does with the caller identity.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CallerIdentityRole {
    /// The body drives a *decision* off `predecessor_account_id`: an
    /// `assert!`/`require!` condition, a rejecting `if` guard, or an `expect` on
    /// a caller-keyed lookup.
    Enforces,
    /// The body returns the resolved caller identity to whoever called it.
    Resolves,
}

/// Classify a function by what it does with `predecessor_account_id`, purely
/// structurally. A body that only mentions the token gets no role at all.
fn classify_caller_identity(sig: &Signature, block: &Block) -> Option<CallerIdentityRole> {
    let taint = predecessor_taint(block);
    let mut visitor = EnforcementVisitor {
        taint: &taint,
        enforced: false,
    };
    visitor.visit_block(block);
    if visitor.enforced {
        return Some(CallerIdentityRole::Enforces);
    }
    if returns_caller_identity(sig, block, &taint) {
        return Some(CallerIdentityRole::Resolves);
    }
    None
}

/// The name of the function/method a call expression targets, if it *is* a call.
fn call_target_name(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Call(ExprCall { func, .. }) => match func.as_ref() {
            Expr::Path(ExprPath { path, .. }) => path.segments.last().map(|s| s.ident.to_string()),
            _ => None,
        },
        Expr::MethodCall(m) => Some(m.method.to_string()),
        _ => None,
    }
}

/// Collects callees whose result is thrown away (`log_storage_event(..);` as a
/// statement). A helper that only *returns* the caller identity cannot possibly
/// authorize a frame that discards what it hands back.
struct DiscardedCalleeCollector {
    calls: Vec<String>,
}

impl<'ast> Visit<'ast> for DiscardedCalleeCollector {
    fn visit_stmt(&mut self, node: &'ast Stmt) {
        if let Stmt::Expr(expr, Some(_)) = node {
            if let Some(name) = call_target_name(expr) {
                self.calls.push(name);
            }
        }
        syn::visit::visit_stmt(self, node);
    }
}

/// Names of callees invoked purely for effect within a block.
fn collect_discarded_callees_block(block: &Block) -> Vec<String> {
    let mut collector = DiscardedCalleeCollector { calls: Vec::new() };
    collector.visit_block(block);
    collector.calls
}

/// Collects the callees a block invokes *with a caller-identity argument*
/// (`self.internal_withdraw(&caller, ..)`). This is what delegation *up* really
/// looks like: the resolved identity has to reach the call site, not merely
/// appear somewhere in the caller's body.
struct IdentityArgCollector<'t> {
    taint: &'t HashSet<String>,
    calls: Vec<String>,
}

impl<'ast, 't> Visit<'ast> for IdentityArgCollector<'t> {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if node
            .args
            .iter()
            .any(|arg| expr_reads_predecessor(arg, self.taint))
        {
            if let Expr::Path(ExprPath { path, .. }) = node.func.as_ref() {
                if let Some(segment) = path.segments.last() {
                    self.calls.push(segment.ident.to_string());
                }
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        if node
            .args
            .iter()
            .any(|arg| expr_reads_predecessor(arg, self.taint))
        {
            self.calls.push(node.method.to_string());
        }
        syn::visit::visit_expr_method_call(self, node);
    }
}

/// Names of callees this block hands a resolved caller identity to.
fn collect_identity_arg_callees(block: &Block) -> Vec<String> {
    let taint = predecessor_taint(block);
    let mut collector = IdentityArgCollector {
        taint: &taint,
        calls: Vec::new(),
    };
    collector.visit_block(block);
    collector.calls
}

/// Visitor that records, for each non-test function/method in the file, what it
/// does with the caller identity and which callees it passes that identity to.
struct FnDefCollector {
    roles: HashMap<String, CallerIdentityRole>,
    identity_args: HashMap<String, Vec<String>>,
}

impl FnDefCollector {
    fn record(&mut self, name: String, sig: &Signature, block: &Block) {
        if let Some(role) = classify_caller_identity(sig, block) {
            self.roles.insert(name.clone(), role);
        }
        self.identity_args
            .insert(name, collect_identity_arg_callees(block));
    }
}

impl<'ast> Visit<'ast> for FnDefCollector {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        if !is_test_fn(&func.attrs) {
            self.record(func.sig.ident.to_string(), &func.sig, &func.block);
        }
        syn::visit::visit_item_fn(self, func);
    }

    fn visit_impl_item_fn(&mut self, func: &'ast syn::ImplItemFn) {
        if !is_test_fn(&func.attrs) {
            self.record(func.sig.ident.to_string(), &func.sig, &func.block);
        }
        syn::visit::visit_impl_item_fn(self, func);
    }
}

/// Collects call/method-call target names from an expression tree.
struct CalleeCollector {
    calls: Vec<String>,
}

impl<'ast> Visit<'ast> for CalleeCollector {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let Expr::Path(ExprPath { path, .. }) = node.func.as_ref() {
            if let Some(segment) = path.segments.last() {
                self.calls.push(segment.ident.to_string());
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        self.calls.push(node.method.to_string());
        syn::visit::visit_expr_method_call(self, node);
    }
}

struct StorageVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    roles: &'a HashMap<String, CallerIdentityRole>,
    identity_args: &'a HashMap<String, Vec<String>>,
}

impl<'a> StorageVisitor<'a> {
    /// Authorization delegated *down*: the flagged function calls a same-file
    /// helper that actually acts on `predecessor_account_id` (idiomatic
    /// `assert_registered_caller()` / `assert_owner()` factoring).
    ///
    /// The helper must *do* something with the caller identity, not merely
    /// mention it: a helper that formats the caller into a log line performs no
    /// comparison and no assertion, and suppressing on it hides a real drain.
    fn auth_in_callees(&self, func: &ItemFn) -> bool {
        let callees = collect_callees_block(&func.block);
        let discarded = collect_discarded_callees_block(&func.block);
        callees.iter().any(|callee| match self.roles.get(callee) {
            // A helper that asserts on the caller authorizes this frame however
            // its result is used — the assertion fires either way.
            Some(CallerIdentityRole::Enforces) => true,
            // A helper that only *resolves* the identity authorizes nothing
            // unless this frame actually consumes what it hands back.
            Some(CallerIdentityRole::Resolves) => {
                let total = callees.iter().filter(|c| *c == callee).count();
                let dropped = discarded.iter().filter(|c| *c == callee).count();
                total > dropped
            }
            None => false,
        })
    }

    /// Authorization delegated *up*: a trusted same-file caller resolves the
    /// predecessor identity and passes it *into* this function as an argument
    /// (the NEP-145 public/internal layering).
    ///
    /// Requires the identity to reach the call site. A caller that merely
    /// mentions `predecessor_account_id` somewhere else in its body (logging it,
    /// say) delegates nothing and must not suppress the finding.
    fn auth_in_callers(&self, fn_name: &str) -> bool {
        self.identity_args
            .iter()
            .any(|(caller, callees)| caller != fn_name && callees.iter().any(|c| c == fn_name))
    }
}

impl<'ast, 'a> Visit<'ast> for StorageVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // `#[cfg(test)]` modules are not deployed on-chain — their functions are
        // not contract entry points even when their names contain the substring.
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test-harness functions (`test_storage_withdraw_*` etc.).
        if is_test_fn(&func.attrs) {
            return;
        }

        let fn_name = func.sig.ident.to_string();

        // Only check storage-related handlers.
        let is_deposit = fn_name.contains("storage_deposit");
        let is_withdraw = fn_name.contains("storage_withdraw");
        let is_unregister = fn_name.contains("storage_unregister");
        if !is_deposit && !is_withdraw && !is_unregister {
            return;
        }

        let body_src = fn_body_source(func);

        // A finding only makes sense for a handler that performs an action worth
        // authorizing: a `&mut self` receiver, or a body that mutates state /
        // moves funds. Pure `&self` view getters (e.g. `min_storage_deposit_amount`)
        // change nothing and transfer nothing, so there is nothing to authorize.
        let receiver_is_mut = func
            .sig
            .receiver()
            .map_or(false, |r| r.mutability.is_some());
        let has_effect = body_src.contains("insert")
            || body_src.contains("remove")
            || body_src.contains("transfer")
            || body_src.contains("Promise");
        if !receiver_is_mut && !has_effect {
            return;
        }

        // NEP-145 makes `storage_deposit` permissionless: anyone may pay storage
        // on behalf of any account using their OWN attached deposit. When the
        // beneficiary is a required `AccountId` parameter (never defaulted from
        // the caller) and the body moves no funds out, `predecessor_account_id`
        // is not required. `storage_withdraw` / `storage_unregister` keep the
        // strict check.
        if is_deposit && !is_withdraw && !is_unregister {
            let permissionless = has_required_account_id_param(&func.sig)
                && !body_src.contains("Promise")
                && !body_src.contains("transfer");
            if permissionless {
                return;
            }
        }

        // Direct predecessor check in the handler's own body.
        if body_src.contains("predecessor_account_id") {
            return;
        }

        // Authorization factored into a resolved same-file callee (helper) whose
        // body reads predecessor_account_id.
        if self.auth_in_callees(func) {
            return;
        }

        // Internal helper (`internal_*` / `*_impl` / `*_unchecked`) that receives
        // an already-resolved account identity and whose trusted same-file caller
        // performs the predecessor check. Requires a RESOLVED caller that actually
        // reads predecessor_account_id — not a name-only skip.
        let is_internal_shaped = fn_name.starts_with("internal_")
            || fn_name.ends_with("_impl")
            || fn_name.ends_with("_unchecked");
        if is_internal_shaped && has_account_id_param(&func.sig) && self.auth_in_callers(&fn_name) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "NEAR-003".to_string(),
            name: "storage-staking-auth".to_string(),
            severity: Severity::High,
            confidence: Confidence::Medium,
            message: format!(
                "Storage handler '{}' does not check predecessor_account_id",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Use env::predecessor_account_id() to identify the caller and validate authorization".to_string(),
            chain: Chain::Near,
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
            Chain::Near,
            std::collections::HashMap::new(),
        );
        StorageStakingDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_auth() {
        let source = r#"
            fn storage_withdraw(&mut self, amount: Option<U128>) -> bool {
                self.internal_storage_withdraw(amount.map(|a| a.0));
                true
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect missing predecessor check"
        );
    }

    #[test]
    fn test_no_finding_with_auth() {
        let source = r#"
            fn storage_withdraw(&mut self, amount: Option<U128>) -> bool {
                let account_id = env::predecessor_account_id();
                self.internal_storage_withdraw(&account_id, amount.map(|a| a.0));
                true
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with predecessor check"
        );
    }

    // FP idx 0: internal helper receiving an already-authorized account_id. Its
    // trusted same-file caller resolves predecessor_account_id and passes the
    // account down, so the helper needs no check of its own.
    #[test]
    fn test_no_finding_internal_helper_with_authorized_caller() {
        let source = r#"
            fn storage_withdraw(&mut self, amount: Option<U128>) -> bool {
                let account_id = env::predecessor_account_id();
                self.internal_storage_withdraw(&account_id, amount.map(|a| a.0));
                true
            }
            fn internal_storage_withdraw(&mut self, account_id: &AccountId, amount: Option<Balance>) -> StorageBalance {
                let mut balance = self.accounts.get(account_id).expect("not registered");
                let to_withdraw = amount.unwrap_or(balance.available);
                balance.available -= to_withdraw;
                self.accounts.insert(account_id, &balance);
                Promise::new(account_id.clone()).transfer(to_withdraw);
                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Internal helper with an authorized caller should not be flagged"
        );
    }

    // FP idx 1: authorization performed via a helper method that wraps
    // predecessor_account_id (resolved as a same-file callee).
    #[test]
    fn test_no_finding_auth_via_resolved_helper() {
        let source = r#"
            fn storage_unregister(&mut self, force: Option<bool>) -> bool {
                assert_one_yocto();
                let account_id = self.assert_registered_caller();
                self.internal_unregister(&account_id, force.unwrap_or(false))
            }
            fn assert_registered_caller(&self) -> AccountId {
                let caller = env::predecessor_account_id();
                assert!(self.accounts.contains_key(&caller), "not registered");
                caller
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Auth factored into a resolved helper should not be flagged"
        );
    }

    // FP idx 1 soundness: a helper that does NOT resolve predecessor_account_id
    // must NOT suppress the finding (no false negative).
    #[test]
    fn test_flags_when_helper_lacks_predecessor() {
        let source = r#"
            fn storage_unregister(&mut self, force: Option<bool>) -> bool {
                let account_id = self.some_unrelated_helper();
                self.internal_unregister(&account_id, force.unwrap_or(false))
            }
            fn some_unrelated_helper(&self) -> AccountId {
                self.default_account.clone()
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Helper without a predecessor check must not suppress the finding"
        );
    }

    // FP idx 2: NEP-145 storage_deposit is permissionless by design when it
    // credits a required account_id and moves no funds out.
    #[test]
    fn test_no_finding_permissionless_storage_deposit() {
        let source = r#"
            #[payable]
            pub fn storage_deposit(&mut self, account_id: AccountId) -> StorageBalance {
                let deposit = env::attached_deposit();
                require!(deposit >= self.min.0, "deposit too low");
                let mut balance = self.accounts.get(&account_id).unwrap_or_default();
                balance.total += deposit;
                self.accounts.insert(&account_id, &balance);
                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Permissionless NEP-145 storage_deposit should not be flagged"
        );
    }

    // FP idx 3: read-only view/getter whose name contains the substring but
    // mutates nothing and moves no funds.
    #[test]
    fn test_no_finding_readonly_getter() {
        let source = r#"
            pub fn min_storage_deposit_amount(&self) -> U128 {
                U128(Balance::from(self.storage_bounds.min))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Read-only getter should not be flagged"
        );
    }

    // FP idx 4: unit-test functions inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                #[test]
                fn test_storage_withdraw_rejects_unregistered() {
                    let mut contract = Contract::new();
                    contract.storage_withdraw(None);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Test-harness functions should not be flagged"
        );
    }

    // REGRESSION (ADV-206 false negative). The `auth_in_callees` guard skipped
    // any handler that called a same-file helper whose body merely *contained*
    // the `predecessor_account_id` token. `log_storage_event` below only formats
    // the caller into a log line — no comparison, no assertion — so it cannot
    // authorize anything, yet it silenced the detector on a handler that lets
    // anyone drain any account's staked storage deposit:
    // `storage_withdraw(victim.near, attacker.near, victim_balance)`.
    #[test]
    fn test_still_flags_withdraw_when_helper_only_logs_caller() {
        let source = r#"
            fn log_storage_event(kind: &str, subject: &AccountId) {
                env::log_str(&format!(
                    "storage_event kind={} subject={} caller={}",
                    kind,
                    subject,
                    env::predecessor_account_id()
                ));
            }

            #[payable]
            pub fn storage_withdraw(
                &mut self,
                account_id: AccountId,
                receiver_id: Option<AccountId>,
                amount: U128,
            ) -> StorageBalance {
                log_storage_event("withdraw", &account_id);

                let mut balance = self.accounts.get(&account_id).expect("not registered");
                let to_withdraw: Balance = amount.0;
                assert!(balance.available >= to_withdraw, "insufficient available");

                balance.available -= to_withdraw;
                balance.total -= to_withdraw;
                self.accounts.insert(&account_id, &balance);

                let beneficiary = receiver_id.unwrap_or(account_id);
                Promise::new(beneficiary).transfer(to_withdraw);

                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.detector_id == "NEAR-003"),
            "Handler whose helper only logs the caller must still be flagged"
        );
    }

    // Same bug class, message position: the caller appears only in an assertion's
    // *format arguments*. `assert!(cond, "denied for {}", caller)` decides nothing
    // about the caller and must not suppress.
    #[test]
    fn test_still_flags_when_caller_only_in_assert_message() {
        let source = r#"
            fn require_liquidity(&self, needed: Balance) {
                assert!(
                    self.pool >= needed,
                    "insufficient pool for {}",
                    env::predecessor_account_id()
                );
            }
            pub fn storage_withdraw(&mut self, account_id: AccountId, amount: U128) -> StorageBalance {
                self.require_liquidity(amount.0);
                let mut balance = self.accounts.get(&account_id).expect("not registered");
                balance.available -= amount.0;
                self.accounts.insert(&account_id, &balance);
                Promise::new(account_id).transfer(amount.0);
                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.detector_id == "NEAR-003"),
            "Caller mentioned only in an assert message must not suppress the finding"
        );
    }

    // Same bug class, delegation *up*: a caller that only logs the predecessor
    // hands no identity down, so the internal helper is still unauthorized.
    #[test]
    fn test_still_flags_internal_helper_when_caller_only_logs_predecessor() {
        let source = r#"
            pub fn storage_withdraw(&mut self, account_id: AccountId, amount: Option<U128>) -> bool {
                env::log_str(&format!("caller={}", env::predecessor_account_id()));
                self.internal_storage_withdraw(&account_id, amount.map(|a| a.0));
                true
            }
            fn internal_storage_withdraw(&mut self, account_id: &AccountId, amount: Option<Balance>) -> StorageBalance {
                let mut balance = self.accounts.get(account_id).expect("not registered");
                let to_withdraw = amount.unwrap_or(balance.available);
                balance.available -= to_withdraw;
                self.accounts.insert(account_id, &balance);
                Promise::new(account_id.clone()).transfer(to_withdraw);
                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings
                .iter()
                .any(|f| f.message.contains("internal_storage_withdraw")),
            "Internal helper whose caller only logs the predecessor must still be flagged"
        );
    }

    // A helper that resolves the caller identity but whose result the handler
    // throws away authorizes nothing.
    #[test]
    fn test_still_flags_when_resolver_result_discarded() {
        let source = r#"
            fn resolve_caller(&self) -> AccountId {
                env::predecessor_account_id()
            }
            pub fn storage_withdraw(&mut self, account_id: AccountId, amount: U128) -> StorageBalance {
                self.resolve_caller();
                let mut balance = self.accounts.get(&account_id).expect("not registered");
                balance.available -= amount.0;
                self.accounts.insert(&account_id, &balance);
                Promise::new(account_id).transfer(amount.0);
                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.detector_id == "NEAR-003"),
            "Discarded identity resolver must not suppress the finding"
        );
    }

    // Converse of the above: a helper that resolves the caller identity AND whose
    // result the handler actually uses is genuine authorization.
    #[test]
    fn test_no_finding_when_resolver_result_used() {
        let source = r#"
            fn resolve_caller(&self) -> AccountId {
                env::predecessor_account_id()
            }
            pub fn storage_withdraw(&mut self, amount: U128) -> StorageBalance {
                let account_id = self.resolve_caller();
                let mut balance = self.accounts.get(&account_id).expect("not registered");
                balance.available -= amount.0;
                self.accounts.insert(&account_id, &balance);
                Promise::new(account_id).transfer(amount.0);
                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Consumed identity resolver is real authorization and should not be flagged"
        );
    }

    // A rejecting `if` guard on the caller is enforcement even without a macro.
    #[test]
    fn test_no_finding_auth_via_rejecting_if_guard() {
        let source = r#"
            fn assert_owner(&self) {
                if env::predecessor_account_id() != self.owner {
                    env::panic_str("unauthorized");
                }
            }
            pub fn storage_withdraw(&mut self, account_id: AccountId, amount: U128) -> StorageBalance {
                self.assert_owner();
                let mut balance = self.accounts.get(&account_id).expect("not registered");
                balance.available -= amount.0;
                self.accounts.insert(&account_id, &balance);
                Promise::new(account_id).transfer(amount.0);
                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Rejecting if-guard on the caller should not be flagged"
        );
    }

    // Soundness: a genuinely unauthorized withdraw handler is still flagged.
    #[test]
    fn test_flags_unauthorized_withdraw() {
        let source = r#"
            pub fn storage_withdraw(&mut self, amount: Option<U128>) -> StorageBalance {
                let mut balance = self.accounts.get(&self.some_account).unwrap();
                balance.available -= amount.map(|a| a.0).unwrap_or(balance.available);
                self.accounts.insert(&self.some_account, &balance);
                balance
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Unauthorized withdraw handler must still be flagged"
        );
    }
}
