use quote::ToTokens;
use syn::visit::Visit;
use syn::{ExprMethodCall, ImplItemFn, Macro};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct PanicUsageDetector;

impl Detector for PanicUsageDetector {
    fn id(&self) -> &'static str {
        "INK-007"
    }
    fn name(&self) -> &'static str {
        "ink-panic-usage"
    }
    fn description(&self) -> &'static str {
        "Detects unwrap(), expect(), panic!() in ink message/constructor functions"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Ink
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = PanicVisitor {
            findings: &mut findings,
            ctx,
            current_fn: None,
            guards: Vec::new(),
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// A guard observed earlier in the same message body that proves a later
/// `.unwrap()`/`.expect()` cannot panic. Captured with the source line so we
/// only honour guards that textually precede the unwrap.
#[derive(Clone)]
enum Guard {
    /// `X.contains(k)` / `X.contains_key(k)` — proves key `k` exists in map `X`.
    Contains {
        base: String,
        key: String,
        line: usize,
    },
    /// `<expr>.is_some()/is_none()/is_ok()/is_err()` — proves `<expr>` is checked.
    Option { receiver: String, line: usize },
}

/// Collect containment / option guards inside a message body so a subsequent
/// provably-safe unwrap on the same receiver can be excluded.
struct GuardCollector {
    guards: Vec<Guard>,
}

impl<'ast> Visit<'ast> for GuardCollector {
    fn visit_expr_method_call(&mut self, call: &'ast ExprMethodCall) {
        let method = call.method.to_string();
        let line = span_to_line(&call.method.span());
        match method.as_str() {
            "contains" | "contains_key" => {
                let base = call.receiver.to_token_stream().to_string();
                if let Some(arg) = call.args.first() {
                    let key = arg.to_token_stream().to_string();
                    self.guards.push(Guard::Contains { base, key, line });
                }
            }
            "is_some" | "is_none" | "is_ok" | "is_err" => {
                let receiver = call.receiver.to_token_stream().to_string();
                self.guards.push(Guard::Option { receiver, line });
            }
            _ => {}
        }
        syn::visit::visit_expr_method_call(self, call);
    }
}

/// True when `e` is a compile-time-constant argument (an integer/float/etc.
/// literal, or a negated / grouped / parenthesised literal). Used to recognise
/// provably-infallible constructions like `NonZeroU128::new(1000)`.
fn is_const_arg(e: &syn::Expr) -> bool {
    match e {
        syn::Expr::Lit(_) => true,
        syn::Expr::Unary(u) => matches!(u.op, syn::UnOp::Neg(_)) && is_const_arg(&u.expr),
        syn::Expr::Group(g) => is_const_arg(&g.expr),
        syn::Expr::Paren(p) => is_const_arg(&p.expr),
        _ => false,
    }
}

struct PanicVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    current_fn: Option<String>,
    guards: Vec<Guard>,
}

impl<'a> PanicVisitor<'a> {
    /// Decide whether an `.unwrap()`/`.expect()` at `unwrap_line` is provably
    /// guarded by an earlier `contains`/`is_some`/... check on the same
    /// receiver, and therefore should not be flagged.
    fn is_guarded_unwrap(&self, call: &ExprMethodCall, unwrap_line: usize) -> bool {
        let receiver_tokens = call.receiver.to_token_stream().to_string();

        // Case 1: `X.get(k).is_some()` / `.is_none()` / `.is_ok()` / `.is_err()`
        // earlier, then `X.get(k).unwrap()` — receiver expressions match exactly.
        for g in &self.guards {
            if let Guard::Option { receiver, line } = g {
                if *line < unwrap_line && *receiver == receiver_tokens {
                    return true;
                }
            }
        }

        // Case 2: `X.contains(k)` earlier, then `X.get(k).unwrap()` — match the
        // map base and the key argument of the `.get()` call.
        if let syn::Expr::MethodCall(inner) = &*call.receiver {
            let inner_method = inner.method.to_string();
            if inner_method == "get" || inner_method == "get_mut" {
                let base = inner.receiver.to_token_stream().to_string();
                if let Some(arg) = inner.args.first() {
                    let key = arg.to_token_stream().to_string();
                    for g in &self.guards {
                        if let Guard::Contains {
                            base: gb,
                            key: gk,
                            line,
                        } = g
                        {
                            if *line < unwrap_line && *gb == base && *gk == key {
                                return true;
                            }
                        }
                    }
                }
            }
        }

        false
    }
}

impl<'ast, 'a> Visit<'ast> for PanicVisitor<'a> {
    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        // Only real ink! entry points count. Using has_nested_attribute (which
        // requires the attribute path ident to be exactly `ink` before looking
        // at the nested tokens) avoids matching #[doc = "...ink...message..."]
        // comments or #[cfg(feature = "ink-message-...")] attributes that merely
        // contain the substrings "ink" and "message"/"constructor".
        let has_ink_attr = has_nested_attribute(&method.attrs, "ink", "message")
            || has_nested_attribute(&method.attrs, "ink", "constructor");

        if has_ink_attr {
            let mut collector = GuardCollector { guards: Vec::new() };
            collector.visit_block(&method.block);

            let prev_fn = self.current_fn.take();
            let prev_guards = std::mem::take(&mut self.guards);

            self.current_fn = Some(method.sig.ident.to_string());
            self.guards = collector.guards;
            syn::visit::visit_impl_item_fn(self, method);

            self.current_fn = prev_fn;
            self.guards = prev_guards;
        }
    }

    fn visit_expr_method_call(&mut self, call: &'ast ExprMethodCall) {
        if self.current_fn.is_none() {
            syn::visit::visit_expr_method_call(self, call);
            return;
        }

        let method = call.method.to_string();
        if method == "unwrap" || method == "expect" {
            // Skip checked_*.unwrap() - the checked_ already guards against overflow
            // e.g., self.value.checked_add(delta).unwrap() is safe arithmetic
            let receiver_src = call.receiver.to_token_stream().to_string();
            if receiver_src.contains("checked_") {
                syn::visit::visit_expr_method_call(self, call);
                return;
            }

            // Skip provably-infallible constructions: a call whose arguments are
            // all compile-time literals, e.g. NonZeroU128::new(1000).unwrap() or
            // u128::try_from(5).unwrap(). Their failure is statically impossible
            // and cannot depend on contract state or attacker input. This is
            // syntactically narrow: data-dependent unwraps like
            // map.get(&key).unwrap() have a method-call (not call) receiver whose
            // argument is not a literal, so they are unaffected.
            if let syn::Expr::Call(inner) = &*call.receiver {
                if !inner.args.is_empty() && inner.args.iter().all(is_const_arg) {
                    syn::visit::visit_expr_method_call(self, call);
                    return;
                }
            }

            // Skip unwraps that are provably guarded by an earlier
            // contains()/is_some()/is_ok() check on the same receiver.
            let line = span_to_line(&call.method.span());
            if self.is_guarded_unwrap(call, line) {
                syn::visit::visit_expr_method_call(self, call);
                return;
            }

            self.findings.push(Finding {
                detector_id: "INK-007".to_string(),
                name: "ink-panic-usage".to_string(),
                severity: Severity::High,
                confidence: Confidence::High,
                message: format!(
                    "{}() used in ink! message/constructor '{}'",
                    method,
                    self.current_fn.as_ref().unwrap()
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&call.method.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: format!(
                    "Replace .{}() with proper error handling using Result return type",
                    method
                ),
                chain: Chain::Ink,
            });
        }

        syn::visit::visit_expr_method_call(self, call);
    }

    fn visit_macro(&mut self, mac: &'ast Macro) {
        if self.current_fn.is_none() {
            return;
        }

        let path_str = mac.path.to_token_stream().to_string();
        if path_str == "panic" || path_str == "todo" || path_str == "unimplemented" {
            if let Some(seg) = mac.path.segments.first() {
                let line = span_to_line(&seg.ident.span());
                self.findings.push(Finding {
                    detector_id: "INK-007".to_string(),
                    name: "ink-panic-usage".to_string(),
                    severity: Severity::High,
                    confidence: Confidence::High,
                    message: format!(
                        "{}!() used in ink! message/constructor '{}'",
                        path_str,
                        self.current_fn.as_ref().unwrap()
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&seg.ident.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Return a proper error instead of panicking in ink! messages"
                        .to_string(),
                    chain: Chain::Ink,
                });
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
            Chain::Ink,
            std::collections::HashMap::new(),
        );
        PanicUsageDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unwrap_in_message() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn get_value(&self) -> u32 {
                    self.map.get(&key).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect unwrap in ink message");
    }

    #[test]
    fn test_no_finding_checked_unwrap() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn inc_by(&mut self, delta: u64) {
                    self.value = self.value.checked_add(delta).unwrap();
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag checked_add().unwrap()"
        );
    }

    #[test]
    fn test_no_finding_in_helper() {
        let source = r#"
            impl MyContract {
                fn helper(&self) -> u32 {
                    self.map.get(&key).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag unwrap in helper");
    }

    // FP idx=1: a doc comment whose text contains the substrings "ink"
    // (e.g. inside "Links") and "message" must NOT turn a private helper into
    // an ink! message. This is the same helper case test_no_finding_in_helper
    // asserts, but with the doc comment that previously tripped the substring
    // attribute check.
    #[test]
    fn test_no_finding_doc_comment_helper() {
        let source = r#"
            impl MyContract {
                /// Links the message sender to a profile record.
                fn resolve_profile(&self) -> u32 {
                    self.map.get(&key).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Doc comment with 'ink'/'message' substrings must not mark a helper as an ink message"
        );
    }

    // FP idx=1 companion: a cfg attribute containing the substrings must also
    // not be treated as an ink! message attribute.
    #[test]
    fn test_no_finding_cfg_feature_helper() {
        let source = r#"
            impl MyContract {
                #[cfg(feature = "ink-message-compat")]
                fn compat_helper(&self) -> u32 {
                    self.map.get(&key).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "cfg attribute with 'ink'/'message' substrings must not mark a helper as an ink message"
        );
    }

    // FP idx=0: unwrap provably guarded by a preceding contains() check on the
    // same map and key must not be flagged.
    #[test]
    fn test_no_finding_guarded_by_contains() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn balance_of(&self, owner: AccountId) -> Balance {
                    if !self.balances.contains(&owner) {
                        return 0;
                    }
                    self.balances.get(&owner).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag unwrap guarded by a preceding contains() on the same key"
        );
    }

    // FP idx=0 companion: unwrap guarded by a preceding is_none() check on the
    // exact same receiver expression must not be flagged.
    #[test]
    fn test_no_finding_guarded_by_is_some() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn balance_of(&self, owner: AccountId) -> Balance {
                    if self.balances.get(&owner).is_none() {
                        return 0;
                    }
                    self.balances.get(&owner).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag unwrap guarded by a preceding is_none() on the same receiver"
        );
    }

    // FP idx=0 soundness: a contains() on a DIFFERENT key must NOT suppress the
    // unwrap — this ensures the guard is narrow and does not create false
    // negatives.
    #[test]
    fn test_still_flags_unwrap_guarded_on_wrong_key() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn balance_of(&self, owner: AccountId, other: AccountId) -> Balance {
                    if !self.balances.contains(&other) {
                        return 0;
                    }
                    self.balances.get(&owner).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A contains() on a different key must not suppress the unwrap"
        );
    }

    // FP idx=2: provably-infallible construction from a compile-time literal.
    #[test]
    fn test_no_finding_nonzero_literal() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn fee(&self, amount: u128) -> u128 {
                    let rate = core::num::NonZeroU128::new(1000).unwrap();
                    amount / rate.get()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag unwrap on a constructor called with only literal arguments"
        );
    }

    // FP idx=2 soundness: a call with a NON-literal argument must still be
    // flagged (guards against false negatives on data-dependent unwraps).
    #[test]
    fn test_still_flags_call_with_variable_arg() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn fee(&self, divisor: u128, amount: u128) -> u128 {
                    let rate = core::num::NonZeroU128::new(divisor).unwrap();
                    amount / rate.get()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A construction with a variable argument must still be flagged"
        );
    }

    #[test]
    fn test_detects_panic_macro_in_message() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn do_it(&self) {
                    panic!("boom");
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect panic! in ink message");
    }
}
