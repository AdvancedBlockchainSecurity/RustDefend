use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, BinOp, ExprBinary, ItemFn, ItemMod, Local, Macro, Pat};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct SignerVsPredecessorDetector;

impl Detector for SignerVsPredecessorDetector {
    fn id(&self) -> &'static str {
        "NEAR-002"
    }
    fn name(&self) -> &'static str {
        "signer-vs-predecessor"
    }
    fn description(&self) -> &'static str {
        "Detects env::signer_account_id() misuse in access control (should use predecessor)"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Near
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
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
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Never scan `#[cfg(test)]` modules — they are compiled out of the
        // deployed wasm and routinely contain `VMContextBuilder::signer_account_id`
        // setter calls that are not access-control logic.
        if has_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test helpers and test functions (#[test] / #[ink::test] /
        // #[tokio::test]) and any `#[cfg(test)]`-gated function.
        let fn_name = func.sig.ident.to_string();
        if fn_name.contains("test") || is_test_fn(&func.attrs) || has_cfg_test(&func.attrs) {
            return;
        }

        let body_src = fn_body_source(func);
        if !body_src.contains("signer_account_id") {
            syn::visit::visit_item_fn(self, func);
            return;
        }

        // Collect local bindings that alias env::signer_account_id() /
        // env::predecessor_account_id() so that access-control checks written
        // against those locals are still understood.
        let mut signer_vars: Vec<String> = Vec::new();
        let mut pred_vars: Vec<String> = Vec::new();
        collect_bound_vars(&func.block, &mut signer_vars, &mut pred_vars);

        // Walk the body at expression granularity: only flag when
        // signer_account_id is an operand of an access-control check
        // (assert!/require! macro or an == / != comparison) AND that check is
        // NOT the canonical `signer == predecessor` direct-call guard.
        let mut acv = AccessControlVisitor {
            signer_vars: &signer_vars,
            pred_vars: &pred_vars,
            violation: false,
        };
        acv.visit_block(&func.block);

        if acv.violation {
            let line = span_to_line(&func.sig.ident.span());
            // Find the actual line with signer_account_id for better reporting.
            let signer_line = self
                .ctx
                .source
                .lines()
                .enumerate()
                .find(|(_, l)| {
                    let t = l.trim();
                    t.contains("signer_account_id")
                        && !t.starts_with("//")
                        && !t.starts_with("///")
                        && !t.starts_with("*")
                })
                .map(|(i, _)| i + 1)
                .unwrap_or(line);

            self.findings.push(Finding {
                detector_id: "NEAR-002".to_string(),
                name: "signer-vs-predecessor".to_string(),
                severity: Severity::High,
                confidence: Confidence::High,
                message: format!(
                    "Function '{}' uses signer_account_id() for access control instead of predecessor_account_id()",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line: signer_line,
                column: 1,
                snippet: snippet_at_line(&self.ctx.source, signer_line),
                recommendation: "Use env::predecessor_account_id() for access control. signer_account_id() returns the transaction originator which can differ from the direct caller in cross-contract calls".to_string(),
                chain: Chain::Near,
            });
        }

        syn::visit::visit_item_fn(self, func);
    }
}

/// Inner visitor that inspects only genuine access-control expressions.
struct AccessControlVisitor<'v> {
    signer_vars: &'v [String],
    pred_vars: &'v [String],
    violation: bool,
}

impl<'v> AccessControlVisitor<'v> {
    /// True if the token text uses `env::signer_account_id()` (or a local that
    /// aliases it) — NOT a `.signer_account_id(...)` setter, NOT a string literal.
    fn refs_signer(&self, tokens: &str) -> bool {
        is_env_call(tokens, "signer_account_id") || tokens_contain_ident(tokens, self.signer_vars)
    }

    /// True if the token text uses `env::predecessor_account_id()` (or a local
    /// that aliases it). Requires an actual call — a string literal mentioning
    /// "predecessor_account_id" must NOT exempt a real signer misuse.
    fn refs_pred(&self, tokens: &str) -> bool {
        is_env_call(tokens, "predecessor_account_id")
            || tokens_contain_ident(tokens, self.pred_vars)
    }
}

impl<'ast, 'v> Visit<'ast> for AccessControlVisitor<'v> {
    fn visit_expr_binary(&mut self, expr: &'ast ExprBinary) {
        if matches!(expr.op, BinOp::Eq(_) | BinOp::Ne(_)) {
            let left = expr.left.to_token_stream().to_string();
            let right = expr.right.to_token_stream().to_string();
            if self.refs_signer(&left) || self.refs_signer(&right) {
                // Skip the documented `signer == predecessor` direct-call guard.
                let is_direct_guard = self.refs_pred(&left) || self.refs_pred(&right);
                if !is_direct_guard {
                    self.violation = true;
                }
            }
        }
        syn::visit::visit_expr_binary(self, expr);
    }

    fn visit_macro(&mut self, mac: &'ast Macro) {
        if is_assertion_macro(mac) {
            let tokens = mac.tokens.to_string();
            // Flag only when signer participates in the assertion and the
            // assertion is not the `signer == predecessor` direct-call guard.
            if self.refs_signer(&tokens) && !self.refs_pred(&tokens) {
                self.violation = true;
            }
        }
        syn::visit::visit_macro(self, mac);
    }
}

/// True if `needle` appears in `tokens` as an actual call (`needle (`) that is
/// NOT a method-call receiver (`. needle (`). This distinguishes
/// `env :: signer_account_id ()` from a `builder . signer_account_id (...)`
/// setter and from a bare string-literal mention.
fn is_env_call(tokens: &str, needle: &str) -> bool {
    let mut from = 0;
    while let Some(rel) = tokens[from..].find(needle) {
        let abs = from + rel;
        let before = tokens[..abs].trim_end();
        let after = tokens[abs + needle.len()..].trim_start();
        let is_call = after.starts_with('(');
        let is_method = before.ends_with('.');
        if is_call && !is_method {
            return true;
        }
        from = abs + needle.len();
    }
    false
}

/// Whole-identifier membership test over a token string. `tokens` produced by
/// `to_token_stream()` is punctuation/space separated, so splitting on
/// non-identifier characters yields clean identifier tokens.
fn tokens_contain_ident(tokens: &str, idents: &[String]) -> bool {
    if idents.is_empty() {
        return false;
    }
    tokens
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .any(|tok| !tok.is_empty() && idents.iter().any(|id| id == tok))
}

/// True for assert!/assert_eq!/assert_ne!/debug_assert*/require!/require_eq!/
/// require_ne! macros (matched on the final path segment).
fn is_assertion_macro(mac: &Macro) -> bool {
    mac.path
        .segments
        .last()
        .map(|seg| {
            matches!(
                seg.ident.to_string().as_str(),
                "assert"
                    | "assert_eq"
                    | "assert_ne"
                    | "debug_assert"
                    | "debug_assert_eq"
                    | "debug_assert_ne"
                    | "require"
                    | "require_eq"
                    | "require_ne"
            )
        })
        .unwrap_or(false)
}

/// Collect local bindings whose initializer is exactly an
/// `env::signer_account_id()` / `env::predecessor_account_id()` call.
fn collect_bound_vars(
    block: &syn::Block,
    signer_vars: &mut Vec<String>,
    pred_vars: &mut Vec<String>,
) {
    struct LocalCollector<'a> {
        signer: &'a mut Vec<String>,
        pred: &'a mut Vec<String>,
    }
    impl<'ast, 'a> Visit<'ast> for LocalCollector<'a> {
        fn visit_local(&mut self, local: &'ast Local) {
            if let Some(init) = &local.init {
                let init_tokens = init.expr.to_token_stream().to_string();
                let refs_signer = is_env_call(&init_tokens, "signer_account_id");
                let refs_pred = is_env_call(&init_tokens, "predecessor_account_id");
                if let Some(name) = pat_ident_name(&local.pat) {
                    if refs_signer && !refs_pred {
                        self.signer.push(name);
                    } else if refs_pred && !refs_signer {
                        self.pred.push(name);
                    }
                }
            }
            syn::visit::visit_local(self, local);
        }
    }
    let mut c = LocalCollector {
        signer: signer_vars,
        pred: pred_vars,
    };
    c.visit_block(block);
}

/// Extract a simple binding identifier from a pattern (`let x` / `let x: T`).
fn pat_ident_name(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Ident(pi) => Some(pi.ident.to_string()),
        Pat::Type(pt) => pat_ident_name(&pt.pat),
        _ => None,
    }
}

/// True if the attribute list marks a test function (#[test] / #[ink::test] /
/// #[tokio::test] — matched on the final `test` segment).
fn is_test_fn(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| {
        a.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

/// True if the attribute list contains `#[cfg(test)]`.
fn has_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|a| {
        if a.path().is_ident("cfg") {
            a.meta.to_token_stream().to_string().contains("test")
        } else {
            false
        }
    })
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
        SignerVsPredecessorDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_signer_in_access_control() {
        let source = r#"
            fn admin_action(&mut self) {
                assert_eq!(env::signer_account_id(), self.owner, "Not owner");
                self.value = 42;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect signer_account_id misuse"
        );
    }

    #[test]
    fn test_no_finding_with_predecessor() {
        let source = r#"
            fn admin_action(&mut self) {
                assert_eq!(env::predecessor_account_id(), self.owner, "Not owner");
                self.value = 42;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag predecessor_account_id"
        );
    }

    // FP idx 0: canonical `assert_eq!(signer, predecessor)` direct-call guard.
    #[test]
    fn test_no_finding_signer_vs_predecessor_direct_guard() {
        let source = r#"
            pub fn claim_airdrop(&mut self) {
                assert_eq!(
                    env::signer_account_id(),
                    env::predecessor_account_id(),
                    "No cross-contract calls allowed"
                );
                self.claim_for(env::predecessor_account_id());
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "signer==predecessor direct-call guard must not be flagged"
        );
    }

    // FP idx 1: access control done via predecessor; signer only in an event.
    #[test]
    fn test_no_finding_signer_only_for_event_attribution() {
        let source = r#"
            pub fn withdraw_all(&mut self) {
                let tx_origin = env::signer_account_id();
                assert_eq!(env::predecessor_account_id(), self.owner);
                Event::Withdraw { by: self.owner.clone(), tx_origin }.emit();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "signer captured only for event attribution must not be flagged"
        );
    }

    // FP idx 2: unrelated `==` counter comparison must not trip access-control.
    #[test]
    fn test_no_finding_unrelated_counter_comparison() {
        let source = r#"
            pub fn ping(&mut self) {
                let tx_origin = env::signer_account_id();
                self.pings += 1;
                if self.pings == 1 {
                    Event::FirstPing { tx_origin }.emit();
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "unrelated counter comparison must not be flagged"
        );
    }

    // FP idx 3: NEAR unit-test context helper inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_vmcontextbuilder_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;
                use near_sdk::test_utils::VMContextBuilder;

                fn get_context(is_owner: bool) -> VMContextBuilder {
                    let mut builder = VMContextBuilder::new();
                    builder
                        .signer_account_id(accounts(if is_owner { 0 } else { 1 }))
                        .predecessor_account_id(accounts(if is_owner { 0 } else { 1 }));
                    builder
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "VMContextBuilder setter inside #[cfg(test)] must not be flagged"
        );
    }

    // Guard against regression: signer misuse expressed as a plain `if` still fires.
    #[test]
    fn test_detects_signer_in_if_comparison() {
        let source = r#"
            fn admin_action(&mut self) {
                if env::signer_account_id() != self.owner {
                    env::panic_str("not owner");
                }
                self.value = 42;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "signer compared against owner in an if must be flagged"
        );
    }
}
