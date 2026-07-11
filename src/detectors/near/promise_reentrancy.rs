use quote::ToTokens;
use syn::visit::Visit;
use syn::ItemFn;

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

/// True if the promise statement chains a `.then(...)` continuation that
/// registers a callback on the contract itself (`ext_self::...`, `Self::ext`,
/// or `ext(env::current_account_id())`). This is the officially recommended
/// NEAR "deduct-then-promise with rollback callback" idiom (checks-effects-
/// interactions with failure recovery), not a reentrancy bug.
fn has_self_rollback_callback(stmt_str: &str) -> bool {
    let has_then = stmt_str.contains(". then (") || stmt_str.contains(".then(");
    if !has_then {
        return false;
    }
    stmt_str.contains("ext_self")
        || stmt_str.contains("Self :: ext")
        || stmt_str.contains("Self::ext")
        || stmt_str.contains("env :: current_account_id")
        || stmt_str.contains("env::current_account_id")
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
                // #[private] rollback callback via `.then(ext_self::...)` is the
                // recommended safe idiom, not a reentrancy bug. Do not fire on
                // this statement; keep scanning in case a later, unprotected
                // promise exists.
                if has_self_rollback_callback(&stmt_str) {
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
