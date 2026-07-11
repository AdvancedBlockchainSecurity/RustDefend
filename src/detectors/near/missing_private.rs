use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, FnArg, ImplItemFn, ItemImpl, ItemMod, Visibility};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingPrivateDetector;

impl Detector for MissingPrivateDetector {
    fn id(&self) -> &'static str {
        "NEAR-006"
    }
    fn name(&self) -> &'static str {
        "missing-private-callback"
    }
    fn description(&self) -> &'static str {
        "Detects public callback methods (on_* / *_callback) without #[private] attribute"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Near
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Require NEAR-specific source markers to avoid cross-chain FPs
        if !ctx.source.contains("near_sdk")
            && !ctx.source.contains("near_contract_standards")
            && !ctx.source.contains("#[near_bindgen]")
            && !ctx.source.contains("#[near(")
            && !ctx.source.contains("env::predecessor_account_id")
            && !ctx.source.contains("env::signer_account_id")
            && !ctx.source.contains("Promise::new")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = PrivateVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct PrivateVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// Returns true if the impl block is a NEAR contract impl, i.e. it carries
/// `#[near_bindgen]` (near-sdk 4) or `#[near]` / `#[near(...)]` (near-sdk 5).
/// Only methods inside such an impl become on-chain entry points; a `pub`
/// method on a plain internal helper struct is ordinary intra-crate Rust API
/// surface that no external account can invoke, so `#[private]` is meaningless
/// there. We match on the last path segment so fully-qualified forms such as
/// `#[near_sdk::near_bindgen]` are still recognised (avoids false negatives).
fn impl_is_contract(node: &ItemImpl) -> bool {
    node.attrs.iter().any(|attr| {
        if let Some(seg) = attr.path().segments.last() {
            let id = seg.ident.to_string();
            id == "near_bindgen" || id == "near"
        } else {
            false
        }
    })
}

/// Returns true if the attribute list contains a `#[cfg(test)]` gate.
/// Code under `#[cfg(test)]` is stripped from the deployed WASM and has no
/// on-chain attack surface, so callbacks on test mocks must not be flagged.
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if attr.path().is_ident("cfg") {
            let tokens = attr.meta.to_token_stream().to_string();
            tokens.contains("test")
        } else {
            false
        }
    })
}

/// Returns true if the method carries evidence that it actually consumes a
/// cross-contract promise result (and is therefore a genuine callback): either
/// a `#[callback_unwrap]` / `#[callback_result]` parameter attribute, or a body
/// that reads promise results. Used to gate weak name matches (`handle_*` and
/// bare `callback` substrings) so ordinary entry points / config setters named
/// after a `callback_*` storage field are not misclassified as callbacks.
fn has_callback_evidence(method: &ImplItemFn, body_src: &str) -> bool {
    if body_src.contains("promise_result")
        || body_src.contains("promise_results_count")
        || body_src.contains("PromiseResult")
    {
        return true;
    }
    method.sig.inputs.iter().any(|arg| {
        if let FnArg::Typed(pat) = arg {
            pat.attrs.iter().any(|a| {
                if let Some(id) = a.path().get_ident() {
                    id == "callback_unwrap" || id == "callback_result"
                } else {
                    false
                }
            })
        } else {
            false
        }
    })
}

/// Returns true if the method body already contains a hand-rolled self-call
/// guard equivalent to what `#[private]` expands to: a comparison of
/// `predecessor_account_id()` against `current_account_id()`, or a call to an
/// `assert_self` helper. Such a method panics for any external caller, so the
/// property `#[private]` protects is already enforced.
fn has_manual_self_guard(body_src: &str) -> bool {
    (body_src.contains("predecessor_account_id") && body_src.contains("current_account_id"))
        || body_src.contains("assert_self")
}

impl<'ast, 'a> Visit<'ast> for PrivateVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Skip #[cfg(test)] modules entirely — their contents never reach WASM.
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
        // Only methods inside a #[near_bindgen] / #[near] contract impl are
        // exported as on-chain entry points and can be reached by an attacker.
        // Plain helper-struct impls carry no callback attack surface.
        if !impl_is_contract(node) {
            return;
        }
        syn::visit::visit_item_impl(self, node);
    }

    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        let fn_name = method.sig.ident.to_string();

        let body_src = method.block.to_token_stream().to_string();

        // Strong callback naming conventions: `on_*` and `*_callback` are the
        // NEAR conventions for `.then()`-registered promise callbacks.
        let strong_signal = fn_name.starts_with("on_") || fn_name.ends_with("_callback");

        // Weak name signals — `handle_*` is a common name for ordinary public
        // entry points, and a bare `callback` substring matches config fields
        // like `callback_gas`. Require actual promise-result evidence before
        // treating these as callbacks.
        let weak_signal = fn_name.starts_with("handle_") || fn_name.contains("callback");

        let is_callback =
            strong_signal || (weak_signal && has_callback_evidence(method, &body_src));

        if !is_callback {
            return;
        }

        // Check if it's public
        let is_public = matches!(method.vis, Visibility::Public(_));
        if !is_public {
            return;
        }

        // Check for #[private] attribute
        let has_private = has_attribute(&method.attrs, "private");
        if has_private {
            return;
        }

        // A hand-rolled self-call guard is byte-for-byte equivalent to the
        // #[private] expansion — the callback is already protected.
        if has_manual_self_guard(&body_src) {
            return;
        }

        let line = span_to_line(&method.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "NEAR-006".to_string(),
            name: "missing-private-callback".to_string(),
            severity: Severity::Critical,
            confidence: Confidence::High,
            message: format!(
                "Callback method '{}' is public without #[private] attribute",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&method.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add #[private] attribute to ensure only the contract itself can call this callback".to_string(),
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
        MissingPrivateDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_private() {
        let source = r#"
            use near_sdk::env;
            #[near_bindgen]
            impl Contract {
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing #[private]");
    }

    #[test]
    fn test_no_finding_with_private() {
        let source = r#"
            impl Contract {
                #[private]
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with #[private]");
    }

    // A genuine `*_callback` callback in a contract impl without #[private]
    // must still fire (guards against over-suppression / false negatives).
    #[test]
    fn test_detects_missing_private_suffix() {
        let source = r#"
            use near_sdk::near_bindgen;
            #[near_bindgen]
            impl Contract {
                pub fn withdraw_callback(&mut self, amount: U128) {
                    self.total -= amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect missing #[private] on *_callback"
        );
    }

    // A genuine `handle_*` callback that reads a promise result must still
    // fire — the weak-name evidence gate keeps real callbacks detectable.
    #[test]
    fn test_detects_handle_callback_with_promise_evidence() {
        let source = r#"
            use near_sdk::env;
            #[near_bindgen]
            impl Contract {
                pub fn handle_swap(&mut self) {
                    let _r = env::promise_result(0);
                    self.total += 1;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "handle_* callback consuming a promise result should be flagged"
        );
    }

    // FP idx 0: pub method on a plain internal helper struct (no #[near_bindgen]).
    #[test]
    fn test_no_finding_on_non_bindgen_helper_struct() {
        let source = r#"
            use near_sdk::near_bindgen;

            pub struct EventRouter;

            impl EventRouter {
                pub fn handle_event(&self, e: &str) -> bool {
                    e.starts_with("transfer")
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "pub method on a non-#[near_bindgen] helper struct is not an entry point"
        );
    }

    // FP idx 1: callback with a hand-rolled self-call guard (manual #[private]).
    #[test]
    fn test_no_finding_with_manual_self_guard() {
        let source = r#"
            use near_sdk::env;
            #[near_bindgen]
            impl Contract {
                pub fn on_transfer_complete(&mut self, amount: U128) {
                    require!(
                        env::predecessor_account_id() == env::current_account_id(),
                        "Only the contract itself can call this callback"
                    );
                    self.total += amount.0;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "hand-rolled self-call guard is equivalent to #[private]"
        );
    }

    // FP idx 2: config setter/getter whose names merely mention a callback_* field.
    #[test]
    fn test_no_finding_on_callback_named_config_methods() {
        let source = r#"
            use near_sdk::near_bindgen;
            #[near_bindgen]
            impl Contract {
                pub fn set_callback_gas(&mut self, gas: u64) {
                    self.assert_owner();
                    self.callback_gas = gas;
                }

                pub fn get_callback_gas(&self) -> u64 {
                    self.callback_gas
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "callback_gas config accessors are not promise callbacks"
        );
    }

    // FP idx 3: handle_* user-facing entry point (no promise-result evidence).
    #[test]
    fn test_no_finding_on_handle_entry_point() {
        let source = r#"
            use near_sdk::env;
            #[near_bindgen]
            impl Contract {
                #[payable]
                pub fn handle_deposit(&mut self) {
                    let who = env::predecessor_account_id();
                    let amount = env::attached_deposit();
                    self.balances.insert(&who, &amount);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "handle_deposit is a plain entry point, not a promise callback"
        );
    }

    // FP idx 4: mock impl inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            use near_sdk::near_bindgen;

            #[cfg(test)]
            mod tests {
                struct MockReceiver { hits: u32 }

                impl MockReceiver {
                    pub fn on_transfer(&mut self) {
                        self.hits += 1;
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "callbacks on test mocks under #[cfg(test)] have no on-chain surface"
        );
    }
}
