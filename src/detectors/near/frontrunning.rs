use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, FnArg, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct FrontrunningDetector;

impl Detector for FrontrunningDetector {
    fn id(&self) -> &'static str {
        "NEAR-008"
    }
    fn name(&self) -> &'static str {
        "frontrunning-risk"
    }
    fn description(&self) -> &'static str {
        "Detects Promise::new().transfer() in functions that take user-provided parameters"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::Low
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
        let mut visitor = FrontrunVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Returns true if the attribute list contains `#[cfg(test)]`.
///
/// Code inside a `#[cfg(test)]` module is compiled only for `cargo test` and is
/// excluded from the deployed wasm artifact, so it has no on-chain attack
/// surface and must never be flagged.
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if !attr.path().is_ident("cfg") {
            return false;
        }
        let tokens = attr.meta.to_token_stream().to_string();
        let compact: String = tokens.chars().filter(|c| !c.is_whitespace()).collect();
        // Matches `cfg(test)` and predicates such as `cfg(all(test,...))`.
        compact.contains("(test)") || compact.contains("(test,") || compact.contains(",test)")
    })
}

/// Returns true if the function carries a test attribute (`#[test]`,
/// `#[tokio::test]`, `#[ink::test]`, `#[near::test]`, ...). Test harness
/// functions are never deployed.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    has_attribute(attrs, "test")
        || has_attribute(attrs, "tokio::test")
        || has_attribute(attrs, "ink::test")
        || has_attribute(attrs, "near::test")
        || has_attribute(attrs, "actix_rt::test")
        || has_attribute(attrs, "async_std::test")
}

/// Returns true if the function's first parameter is a `self` receiver, i.e. it
/// is a method (a potential NEAR entry point) rather than a free helper
/// function. Free functions are never exported by `#[near_bindgen]` and thus
/// have no externally callable / frontrunnable surface of their own.
fn has_self_receiver(func: &ItemFn) -> bool {
    matches!(func.sig.inputs.first(), Some(FnArg::Receiver(_)))
}

struct FrontrunVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for FrontrunVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Skip `#[cfg(test)]` modules entirely — their contents are not deployed
        // on-chain and carry no frontrunning surface (FP: test-fixture helpers).
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test-harness functions.
        if is_test_fn(&func.attrs) {
            return;
        }

        let body_src = fn_body_source(func);

        // Must have a `.transfer(` call.
        if !body_src.contains(".transfer(") && !body_src.contains(". transfer (") {
            return;
        }

        // Native NEAR value transfers are always constructed via `Promise::new(..)`.
        // Requiring the `Promise::new` construction (rather than a bare `Promise`
        // substring) avoids matching internal storage `.transfer()` calls that
        // merely happen to sit next to a `PromiseOrValue`/`PromiseResult` mention.
        if !body_src.contains("Promise::new") && !body_src.contains("Promise :: new") {
            return;
        }

        // Only methods (functions with a `self` receiver) are NEAR entry points.
        // A free helper function is not exported by `#[near_bindgen]`; its
        // parameters are supplied by already-guarded internal callers, so it has
        // no externally callable frontrunning surface.
        if !has_self_receiver(func) {
            return;
        }

        // Require at least one non-self (user-provided) parameter.
        let non_self_params = func.sig.inputs.len().saturating_sub(1);
        if non_self_params == 0 {
            return;
        }

        // Suppress refunds back to the transaction initiator: transferring to
        // `env::predecessor_account_id()` / `env::signer_account_id()` only ever
        // returns the caller their own funds, so there is no shared prize to race
        // for. (Canonical near-contract-standards storage-deposit refund idiom.)
        if body_src.contains("Promise::new(env::predecessor_account_id")
            || body_src.contains("Promise :: new (env :: predecessor_account_id")
            || body_src.contains("Promise::new(env::signer_account_id")
            || body_src.contains("Promise :: new (env :: signer_account_id")
        {
            return;
        }

        // Check for commit-reveal / nonce / deadline frontrunning protection.
        let has_protection = body_src.contains("commit")
            || body_src.contains("reveal")
            || body_src.contains("nonce")
            || body_src.contains("deadline")
            || body_src.contains("block_timestamp");

        // Access-control gating removes the frontrunning race: an owner/2FA guard
        // means there is exactly one authorized caller, so there is no competitive
        // race between mutually untrusted parties to win.
        let has_access_control = (body_src.contains("predecessor_account_id")
            && body_src.contains("owner"))
            || body_src.contains("assert_owner")
            || body_src.contains("only_owner")
            || body_src.contains("require_owner")
            || body_src.contains("assert_one_yocto");

        if !has_protection && !has_access_control {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "NEAR-008".to_string(),
                name: "frontrunning-risk".to_string(),
                severity: Severity::High,
                confidence: Confidence::Low,
                message: format!(
                    "Function '{}' transfers tokens based on user parameters without frontrunning protection",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Consider implementing commit-reveal scheme, deadline parameter, or nonce to prevent frontrunning".to_string(),
                chain: Chain::Near,
            });
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
        FrontrunningDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_frontrunning_risk() {
        let source = r#"
            use near_sdk::Promise;
            fn claim_reward(&mut self, amount: u128, recipient: AccountId) {
                Promise::new(recipient).transfer(amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect frontrunning risk");
    }

    #[test]
    fn test_no_finding_with_deadline() {
        let source = r#"
            use near_sdk::{Promise, env};
            fn claim_reward(&mut self, amount: u128, recipient: AccountId, deadline: u64) {
                assert!(env::block_timestamp() < deadline, "Expired");
                Promise::new(recipient).transfer(amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with deadline protection"
        );
    }

    // FP idx 0: a free helper function (no `self` receiver) is not a NEAR entry
    // point and must not be flagged.
    #[test]
    fn test_no_finding_free_helper_fn() {
        let source = r#"
            use near_sdk::{AccountId, Balance, Promise};
            fn send_payout(recipient: AccountId, amount: Balance) -> Promise {
                Promise::new(recipient).transfer(amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a free (non-entry-point) helper function"
        );
    }

    // FP idx 1: refund of excess attached deposit back to the caller
    // (predecessor_account_id) has no frontrunning value.
    #[test]
    fn test_no_finding_refund_to_predecessor() {
        let source = r#"
            use near_sdk::{env, Balance, Promise};
            fn refund_excess_deposit(&mut self, cost: Balance) {
                let attached = env::attached_deposit();
                if attached > cost {
                    Promise::new(env::predecessor_account_id()).transfer(attached - cost);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a refund back to the transaction initiator"
        );
    }

    // FP idx 2: owner-gated administrative withdrawal has a single authorized
    // caller, so there is no frontrunning race.
    #[test]
    fn test_no_finding_owner_gated_withdraw() {
        let source = r#"
            use near_sdk::{env, AccountId, Promise};
            use near_sdk::json_types::U128;
            pub fn owner_withdraw(&mut self, recipient: AccountId, amount: U128) {
                assert_eq!(env::predecessor_account_id(), self.owner, "Only owner");
                Promise::new(recipient).transfer(amount.0);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag an owner-gated administrative withdrawal"
        );
    }

    // FP idx 3: internal ledger bookkeeping `.transfer()` with a `PromiseOrValue`
    // return is not a native Promise value transfer.
    #[test]
    fn test_no_finding_internal_ledger_transfer() {
        let source = r#"
            use near_sdk::{AccountId, PromiseOrValue};
            fn internal_move(&mut self, from: AccountId, to: AccountId, amount: u128) -> PromiseOrValue<()> {
                self.ledger.transfer(&from, &to, amount);
                PromiseOrValue::Value(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag internal storage .transfer() without Promise::new"
        );
    }

    // FP idx 4: helper functions inside a `#[cfg(test)]` module are never
    // deployed and must not be flagged.
    #[test]
    fn test_no_finding_cfg_test_module() {
        let source = r#"
            use near_sdk::{AccountId, Balance, Promise};

            #[cfg(test)]
            mod tests {
                use super::*;

                fn make_transfer_promise(recipient: AccountId, amount: Balance) -> Promise {
                    Promise::new(recipient).transfer(amount)
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag helpers inside a #[cfg(test)] module"
        );
    }
}
