use quote::ToTokens;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{Attribute, Block, Expr, ExprBinary, ExprCall, ExprMethodCall, ImplItemFn, ItemFn, Stmt};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct PromiseReentrancyDetector;

impl Detector for PromiseReentrancyDetector {
    fn id(&self) -> &'static str {
        "NEAR-001"
    }
    fn name(&self) -> &'static str {
        "promise-reentrancy"
    }
    fn description(&self) -> &'static str {
        "Detects state mutation before Promise::new() / ext_* calls without #[private] callback"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Near
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = ReentrancyVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct ReentrancyVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// True if `s` (a space-separated token-stream rendering) contains a real
/// `ext_*` cross-contract call, i.e. an occurrence of "ext_" that begins a
/// token rather than sitting inside another identifier (`next_id`, `context_`)
/// or inside a string literal (`"ext_transfer"`).
///
/// In a `proc_macro2` token-stream `Display`, tokens are always separated by
/// whitespace, so a genuine `ext_ft` / `ext_self` identifier token is always
/// preceded by whitespace (or is at the very start). "ext_" embedded in a
/// longer identifier is preceded by an alphanumeric char, and "ext_" embedded
/// in a string literal is preceded by `"` — neither is whitespace.
fn contains_ext_call(s: &str) -> bool {
    let bytes = s.as_bytes();
    let needle = b"ext_";
    if bytes.len() < needle.len() {
        return false;
    }
    let mut i = 0;
    while i + needle.len() <= bytes.len() {
        if &bytes[i..i + needle.len()] == needle {
            let at_token_start = i == 0 || bytes[i - 1].is_ascii_whitespace();
            if at_token_start {
                return true;
            }
        }
        i += 1;
    }
    false
}

/// A function defined in the file under scan: name, attributes, body.
type FnDef<'ast> = (String, &'ast [Attribute], &'ast Block);

/// Collects every function defined in the file, free (`fn f()`) or inside an
/// `impl` block, so a `.then(...)`-registered callback can be resolved to its
/// definition and judged on what it *does*.
struct FnDefCollector<'ast> {
    defs: Vec<FnDef<'ast>>,
}

impl<'ast> Visit<'ast> for FnDefCollector<'ast> {
    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        self.defs
            .push((node.sig.ident.to_string(), &node.attrs, &node.block));
        syn::visit::visit_item_fn(self, node);
    }

    fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
        self.defs
            .push((node.sig.ident.to_string(), &node.attrs, &node.block));
        syn::visit::visit_impl_item_fn(self, node);
    }
}

/// Collects the argument expression of every `.then(...)` method call, i.e. the
/// continuations a promise chain registers.
struct ThenArgCollector<'ast> {
    args: Vec<&'ast Expr>,
}

impl<'ast> Visit<'ast> for ThenArgCollector<'ast> {
    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        if node.method == "then" {
            if let Some(arg) = node.args.first() {
                self.args.push(arg);
            }
        }
        syn::visit::visit_expr_method_call(self, node);
    }
}

/// Collects the name of every callee invoked inside an expression: each
/// method-call name and the tail segment of each call path. For
/// `ext_self::ext(env::current_account_id()).on_withdraw_done(amount)` this
/// yields `["ext", "current_account_id", "on_withdraw_done"]` — the candidate
/// names the `.then(...)` continuation could be routing to.
struct CalleeNameCollector {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for CalleeNameCollector {
    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        self.names.push(node.method.to_string());
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let Expr::Path(path) = &*node.func {
            if let Some(seg) = path.path.segments.last() {
                self.names.push(seg.ident.to_string());
            }
        }
        syn::visit::visit_expr_call(self, node);
    }
}

fn callee_names(expr: &Expr) -> Vec<String> {
    let mut collector = CalleeNameCollector { names: Vec::new() };
    collector.visit_expr(expr);
    collector.names
}

/// True if one operand calls `predecessor_account_id()` and the other calls
/// `current_account_id()`, i.e. the two accounts are genuinely being compared
/// *against each other*. Merely mentioning either function (logging the
/// predecessor, passing the current account into a promise) proves nothing.
fn is_predecessor_vs_current(left: &Expr, right: &Expr) -> bool {
    let (l, r) = (callee_names(left), callee_names(right));
    let pairs = |a: &[String], b: &[String]| {
        a.iter().any(|n| n == "predecessor_account_id")
            && b.iter().any(|n| n == "current_account_id")
    };
    pairs(&l, &r) || pairs(&r, &l)
}

/// True if the callback authenticates its caller by actually *comparing*
/// `env::predecessor_account_id()` against `env::current_account_id()` — the
/// hand-rolled equivalent of `#[private]`. The two calls must be operands of
/// the same comparison, whether written as a bare `==` / `!=` (an if-panic
/// guard) or inside an `assert_eq!` / `require_eq!` / `assert!` condition.
struct SelfCallerComparison {
    found: bool,
}

impl<'ast> Visit<'ast> for SelfCallerComparison {
    fn visit_expr_binary(&mut self, node: &'ast ExprBinary) {
        if matches!(node.op, syn::BinOp::Eq(_) | syn::BinOp::Ne(_))
            && is_predecessor_vs_current(&node.left, &node.right)
        {
            self.found = true;
        }
        syn::visit::visit_expr_binary(self, node);
    }

    fn visit_macro(&mut self, node: &'ast syn::Macro) {
        // `assert!` / `require!` / `assert_eq!` bodies are opaque token streams
        // to syn's visitor, so the comparison inside one is invisible unless the
        // tokens are parsed back into expressions.
        let parser = Punctuated::<Expr, syn::Token![,]>::parse_terminated;
        let Ok(args) = parser.parse2(node.tokens.clone()) else {
            return;
        };

        let name = node
            .path
            .segments
            .last()
            .map(|s| s.ident.to_string())
            .unwrap_or_default();

        // `assert_eq!(predecessor, current)` compares its first two arguments
        // rather than evaluating a comparison expression.
        if name.ends_with("_eq") {
            if let (Some(a), Some(b)) = (args.first(), args.iter().nth(1)) {
                if is_predecessor_vs_current(a, b) {
                    self.found = true;
                }
            }
        }

        // `assert!(predecessor == current, ..)` / `require!(..)`: the comparison
        // is an ordinary expression among the arguments.
        for arg in &args {
            self.visit_expr(arg);
        }
    }
}

fn compares_predecessor_to_current(block: &Block) -> bool {
    let mut visitor = SelfCallerComparison { found: false };
    visitor.visit_block(block);
    visitor.found
}

/// True if a promise statement registers a rollback callback that is *verified*
/// to be self-only, so the deduct-then-promise it guards is the recommended
/// NEAR idiom rather than a reentrancy bug.
///
/// What makes that idiom safe is the callback being `#[private]`: near_bindgen
/// then rejects every caller except the contract itself, so only a resolved
/// promise can re-credit state. The safety lives in the callback's definition,
/// never in how the `.then(...)` chain is spelled — `ext_self::` and
/// `env::current_account_id()` in the chain only say *where* the continuation
/// is routed, and an attacker can call an unguarded callback directly without
/// going through the promise at all. So resolve the callback against the
/// functions defined in this file and judge it there: suppress only when a
/// resolved callback is genuinely protected (`#[private]`, or a structural
/// predecessor-vs-current comparison).
///
/// When no named callback resolves to a definition in this file, there is no
/// evidence either way; stay conservative and suppress, matching the behaviour
/// the false-positive pass intended for cross-module callbacks.
fn has_verified_rollback_callback(stmt: &Stmt, file: &syn::File) -> bool {
    let mut then_args = ThenArgCollector { args: Vec::new() };
    then_args.visit_stmt(stmt);
    if then_args.args.is_empty() {
        return false;
    }

    let mut defs = FnDefCollector { defs: Vec::new() };
    defs.visit_file(file);

    let mut resolved_any = false;
    for arg in &then_args.args {
        for name in callee_names(arg) {
            for (def_name, attrs, block) in &defs.defs {
                if *def_name != name {
                    continue;
                }
                resolved_any = true;
                if has_attribute(attrs, "private") || compares_predecessor_to_current(block) {
                    return true;
                }
            }
        }
    }

    // Callback resolved but unguarded => a public credit primitive: fire.
    // Nothing resolved => unknown: keep the conservative suppression.
    !resolved_any
}

impl<'ast, 'a> Visit<'ast> for ReentrancyVisitor<'a> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // A `&self` receiver cannot mutate contract state (Rust borrow rules),
        // so there is no state-before-promise window and no reentrancy of the
        // kind this detector targets. Skip these outright. `&mut self`, `self`,
        // and `mut self` receivers are still analyzed.
        if let Some(receiver) = func.sig.receiver() {
            if receiver.reference.is_some() && receiver.mutability.is_none() {
                return;
            }
        }

        // Analyze the token-stream rendering (consistently space-separated) so
        // substring checks land on real token boundaries.
        let body_src = func.block.to_token_stream().to_string();

        // Must have a Promise::new or a genuine ext_* cross-contract call.
        let has_promise = body_src.contains("Promise :: new")
            || body_src.contains("Promise::new")
            || contains_ext_call(&body_src);

        if !has_promise {
            return;
        }

        // Check for self.field = ... pattern before promise
        let stmts = &func.block.stmts;
        let mut seen_state_mutation = false;

        for stmt in stmts {
            let stmt_str = stmt.to_token_stream().to_string();

            // State mutation patterns
            if stmt_str.contains("self .")
                && stmt_str.contains('=')
                && !stmt_str.contains("==")
                && !stmt_str.contains("!=")
            {
                seen_state_mutation = true;
            }

            let stmt_has_promise = stmt_str.contains("Promise :: new")
                || stmt_str.contains("Promise::new")
                || contains_ext_call(&stmt_str);

            // Promise after state mutation
            if seen_state_mutation && stmt_has_promise {
                // Canonical NEAR deduct-then-promise pattern that registers a
                // rollback callback verified to be #[private] (or equivalently
                // guarded) is the recommended safe idiom, not a reentrancy bug.
                // Do not fire on this statement; keep scanning in case a later,
                // unprotected promise exists.
                if has_verified_rollback_callback(stmt, &self.ctx.ast) {
                    continue;
                }

                let line = span_to_line(&func.sig.ident.span());
                self.findings.push(Finding {
                    detector_id: "NEAR-001".to_string(),
                    name: "promise-reentrancy".to_string(),
                    severity: Severity::Critical,
                    confidence: Confidence::Medium,
                    message: format!(
                        "Function '{}' mutates state before creating a Promise (reentrancy risk)",
                        func.sig.ident
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&func.sig.ident.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Move state mutations to a #[private] callback that executes after the Promise resolves, or use a guard pattern".to_string(),
                    chain: Chain::Near,
                });
                return;
            }
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
            Chain::Near,
            std::collections::HashMap::new(),
        );
        PromiseReentrancyDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_state_before_promise() {
        let source = r#"
            fn withdraw(&mut self, amount: u128) {
                self.balance -= amount;
                Promise::new(receiver).transfer(amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect state mutation before Promise"
        );
    }

    #[test]
    fn test_no_finding_promise_only() {
        let source = r#"
            fn transfer(&self, receiver: AccountId, amount: u128) {
                Promise::new(receiver).transfer(amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when no state mutation"
        );
    }

    // FP1: a `&self` function only reads a field into a local before the
    // transfer; it cannot mutate contract state, so there is no reentrancy
    // window. Must NOT flag.
    #[test]
    fn test_no_finding_readonly_self_ref() {
        let source = r#"
            fn payout(&self, to: AccountId) -> Promise {
                let amount = self.reward_per_user;
                Promise::new(to).transfer(amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Read-only &self helper must not be flagged"
        );
    }

    // FP2: "ext_" matched inside the identifier `next_id` (n-ext_-id); there is
    // no Promise and no cross-contract call at all. Must NOT flag.
    #[test]
    fn test_no_finding_ext_substring_in_identifier() {
        let source = r#"
            fn register(&mut self) -> u64 {
                self.next_id += 1;
                self.next_id
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "'ext_' inside an identifier must not count as a cross-contract call"
        );
    }

    // FP2 (string-literal variant): "ext_" inside a string literal is not a
    // cross-contract call. Must NOT flag.
    #[test]
    fn test_no_finding_ext_in_string_literal() {
        let source = r#"
            fn record(&mut self) {
                self.last_action = "ext_transfer".to_string();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "'ext_' inside a string literal must not count as a cross-contract call"
        );
    }

    // FP4: canonical deduct-then-promise with a registered #[private] rollback
    // callback via `.then(ext_self::...)` is the recommended NEAR idiom. Must
    // NOT flag.
    #[test]
    fn test_no_finding_deduct_then_with_rollback_callback() {
        let source = r#"
            fn withdraw(&mut self, amount: u128) -> Promise {
                self.balance = self.balance - amount;
                Promise::new(env::predecessor_account_id())
                    .transfer(amount)
                    .then(ext_self::ext(env::current_account_id()).on_withdraw_done(amount))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Deduct-then-promise with a self rollback callback must not be flagged"
        );
    }

    // Guard against over-suppression: a genuine mutate-then-ext_ call with NO
    // rollback callback must still fire.
    #[test]
    fn test_still_detects_real_ext_call() {
        let source = r#"
            fn withdraw(&mut self, receiver: AccountId, amount: u128) {
                self.pending = true;
                ext_ft::ext(self.token.clone()).ft_transfer(receiver, amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Real ext_* call after state mutation must still be flagged"
        );
    }

    // MUST STILL FLAG: the probe pattern. The `.then(...)` chain is spelled
    // exactly like the safe rollback idiom — `ext_self::ext(env::current_account_id())`
    // — but the callback it registers is defined right here as a plain public
    // method: no `#[private]`, no caller check. Anyone can invoke
    // `on_withdraw_done(amount)` directly, without any failed promise, and be
    // credited; repeating it mints balance. Suppressing on the spelling of the
    // chain (ADV-206) silenced a genuine, exploitable reentrancy bug.
    #[test]
    fn test_still_flags_then_callback_without_private_attr() {
        let source = r#"
            fn withdraw(&mut self, amount: u128) -> Promise {
                assert!(self.balance >= amount, "insufficient balance");
                self.balance = self.balance - amount;
                Promise::new(env::predecessor_account_id())
                    .transfer(amount)
                    .then(ext_self::ext(env::current_account_id()).on_withdraw_done(amount))
            }

            fn on_withdraw_done(&mut self, amount: u128) {
                self.balance = self.balance + amount;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.message.contains("'withdraw'")),
            "Deduct-then-promise whose .then() callback is a public, non-#[private] \
             credit primitive must be flagged"
        );
    }

    // MUST STILL FLAG (spelling variant): same registration as above, only
    // re-spelled `Self::on_withdraw_done(...)`. Suppression must never depend
    // on how the callback is routed, just on whether it is actually guarded.
    #[test]
    fn test_still_flags_unprotected_callback_alternate_spelling() {
        let source = r#"
            fn withdraw(&mut self, amount: u128) -> Promise {
                self.balance = self.balance - amount;
                Promise::new(env::predecessor_account_id())
                    .transfer(amount)
                    .then(Self::on_withdraw_done(amount))
            }

            fn on_withdraw_done(&mut self, amount: u128) {
                self.balance = self.balance + amount;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.message.contains("'withdraw'")),
            "An unprotected rollback callback must be flagged regardless of spelling"
        );
    }

    // FP4 (strong form): the callback is defined here and really is `#[private]`,
    // so near_bindgen rejects every caller but the contract itself. Genuinely
    // the recommended idiom. Must NOT flag.
    #[test]
    fn test_no_finding_rollback_callback_with_private_attr() {
        let source = r#"
            fn withdraw(&mut self, amount: u128) -> Promise {
                self.balance = self.balance - amount;
                Promise::new(env::predecessor_account_id())
                    .transfer(amount)
                    .then(ext_self::ext(env::current_account_id()).on_withdraw_done(amount))
            }

            #[private]
            fn on_withdraw_done(&mut self, amount: u128) {
                self.balance = self.balance + amount;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A #[private] rollback callback is the safe NEAR idiom and must not be flagged"
        );
    }

    // FP4 (hand-rolled variant): no `#[private]`, but the callback compares
    // predecessor against current account — the manual equivalent. Must NOT flag.
    #[test]
    fn test_no_finding_rollback_callback_with_caller_check() {
        let source = r#"
            fn withdraw(&mut self, amount: u128) -> Promise {
                self.balance = self.balance - amount;
                Promise::new(env::predecessor_account_id())
                    .transfer(amount)
                    .then(ext_self::ext(env::current_account_id()).on_withdraw_done(amount))
            }

            fn on_withdraw_done(&mut self, amount: u128) {
                assert_eq!(
                    env::predecessor_account_id(),
                    env::current_account_id(),
                    "callback is private"
                );
                self.balance = self.balance + amount;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A callback that structurally checks predecessor == current must not be flagged"
        );
    }

    // must_still_fire idx0: mutate/guard-then-Promise with no rollback callback
    // must still fire (regression guard against the receiver/token changes).
    #[test]
    fn test_still_detects_guard_then_promise() {
        let source = r#"
            fn withdraw(&mut self, amount: u128) -> Promise {
                assert!(self.balance >= amount, "insufficient balance");
                Promise::new(env::predecessor_account_id()).transfer(amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "State-touching statement before an unprotected Promise must still fire"
        );
    }
}
