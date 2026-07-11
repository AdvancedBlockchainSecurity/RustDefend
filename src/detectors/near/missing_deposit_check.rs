use std::collections::HashSet;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{ImplItemFn, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingDepositCheckDetector;

impl Detector for MissingDepositCheckDetector {
    fn id(&self) -> &'static str {
        "NEAR-010"
    }
    fn name(&self) -> &'static str {
        "missing-deposit-check"
    }
    fn description(&self) -> &'static str {
        "Detects #[payable] methods that don't check env::attached_deposit()"
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

        // Build an in-file index of functions / impl-methods whose bodies actually
        // perform a deposit-related check (read env::attached_deposit() or assert the
        // mandatory 1 yoctoNEAR). The stock `ScanContext::call_graph` only tracks
        // top-level `fn` items, so it cannot see helpers defined as impl methods
        // (the dominant idiom, e.g. `self.assert_payment_covers(..)`). We resolve the
        // callee bodies here so a check factored one call deep is not a false positive.
        let mut index = DepositCheckerIndex {
            checkers: HashSet::new(),
        };
        index.visit_file(&ctx.ast);

        let mut findings = Vec::new();
        let mut visitor = DepositVisitor {
            findings: &mut findings,
            ctx,
            deposit_checkers: &index.checkers,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// True if a function body performs a deposit-related check. Mirrors the token
/// set the detector already trusts in an immediate method body, so resolving a
/// callee is exactly as strict as the inline check it stands in for.
fn body_has_deposit_check(body_src: &str) -> bool {
    body_src.contains("attached_deposit")
        || body_src.contains("assert_one_yocto")
        || body_src.contains("ONE_YOCTO")
        || body_src.contains("1_000_000_000_000_000_000_000_000")
}

/// Collects the names of every function / impl-method in the file whose body
/// contains a deposit check, so calls to them can be resolved as delegated checks.
struct DepositCheckerIndex {
    checkers: HashSet<String>,
}

impl<'ast> Visit<'ast> for DepositCheckerIndex {
    fn visit_impl_item_fn(&mut self, f: &'ast ImplItemFn) {
        if body_has_deposit_check(&f.block.to_token_stream().to_string()) {
            self.checkers.insert(f.sig.ident.to_string());
        }
        syn::visit::visit_impl_item_fn(self, f);
    }

    fn visit_item_fn(&mut self, f: &'ast ItemFn) {
        if body_has_deposit_check(&f.block.to_token_stream().to_string()) {
            self.checkers.insert(f.sig.ident.to_string());
        }
        syn::visit::visit_item_fn(self, f);
    }
}

/// Collects the names of functions and methods invoked within a block.
struct CallNameCollector {
    names: HashSet<String>,
}

impl<'ast> Visit<'ast> for CallNameCollector {
    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if let syn::Expr::Path(syn::ExprPath { path, .. }) = node.func.as_ref() {
            if let Some(seg) = path.segments.last() {
                self.names.insert(seg.ident.to_string());
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        self.names.insert(node.method.to_string());
        syn::visit::visit_expr_method_call(self, node);
    }
}

struct DepositVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    /// In-file functions/methods whose bodies perform a deposit check.
    deposit_checkers: &'a HashSet<String>,
}

impl<'ast, 'a> Visit<'ast> for DepositVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Do not descend into #[cfg(test)] modules: payable methods on mock/test
        // contracts there are never compiled into the deployed wasm, so an unchecked
        // deposit is not exploitable. The old `test_`-prefix name heuristic missed
        // mocks named after the production method they stand in for.
        if has_attribute_with_value(&module.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        // Check for #[payable] attribute
        let has_payable = has_attribute(&method.attrs, "payable");

        if !has_payable {
            return;
        }

        // #[private] payable methods are promise callbacks: near_bindgen asserts
        // predecessor_account_id == current_account_id, so only the contract itself
        // can invoke them. There is no external payment to validate; #[payable] merely
        // lets the runtime carry the contract's own deposit into the callback.
        if has_attribute(&method.attrs, "private") {
            return;
        }

        let body_src = method.block.to_token_stream().to_string();

        // Check if function references attached_deposit
        let checks_deposit = body_src.contains("attached_deposit")
            || body_src.contains("attached_deposit ()")
            || body_src.contains("attached_deposit()");

        if checks_deposit {
            return;
        }

        // Collect the calls made in this method's body once, for delegation checks.
        let mut collector = CallNameCollector {
            names: HashSet::new(),
        };
        collector.visit_block(&method.block);
        let body_calls = collector.names;

        // The deposit check may be factored into a helper. If this method calls any
        // in-file function/method whose resolved body performs a deposit check
        // (attached_deposit or the 1-yocto assertion), the deposit IS validated.
        if body_calls.iter().any(|c| self.deposit_checkers.contains(c)) {
            return;
        }

        let fn_name = method.sig.ident.to_string();

        // Skip test functions
        if fn_name.starts_with("test_") || fn_name.contains("_test") {
            return;
        }

        // Skip NEP standard methods that handle deposits internally
        // NEP-141 (fungible token), NEP-171 (NFT), NEP-145 (storage management)
        let fn_lower = fn_name.to_lowercase();
        if fn_lower == "ft_transfer"
            || fn_lower == "ft_transfer_call"
            || fn_lower == "nft_transfer"
            || fn_lower == "nft_transfer_call"
            || fn_lower == "nft_mint"
            || fn_lower == "nft_approve"
            || fn_lower == "storage_deposit"
            || fn_lower == "storage_withdraw"
            || fn_lower == "storage_unregister"
            || fn_lower.starts_with("ft_on_")
            || fn_lower.starts_with("nft_on_")
        {
            return;
        }

        // NEP-178 (nft_revoke / nft_revoke_all) and NEP-199 (nft_transfer_payout) are
        // #[payable] purely so the caller must attach exactly 1 yoctoNEAR; the
        // near_contract_standards implementation these wrappers delegate to calls
        // assert_one_yocto() itself. We only skip when the method actually delegates
        // to the same-named standard method (e.g. `self.tokens.nft_revoke(..)`), so a
        // hand-rolled implementation that forgets the yocto guard is still flagged.
        if matches!(
            fn_lower.as_str(),
            "nft_revoke" | "nft_revoke_all" | "nft_transfer_payout"
        ) && body_calls.contains(&fn_name)
        {
            return;
        }

        // Skip admin/owner-only methods where deposit is used as access control
        // These methods use #[payable] to require 1 yoctoNEAR for access control,
        // not to handle arbitrary deposits
        if fn_lower.starts_with("pause")
            || fn_lower.starts_with("resume")
            || fn_lower.starts_with("unpause")
            || fn_lower.starts_with("set_owner")
            || fn_lower.starts_with("set_admin")
            || fn_lower.starts_with("change_owner")
            || fn_lower.starts_with("update_config")
            || fn_lower.starts_with("add_guardian")
            || fn_lower.starts_with("remove_guardian")
            || fn_lower.starts_with("extend_guardians")
            || fn_lower.starts_with("register_")
            || fn_lower.starts_with("unregister_")
            || fn_lower.starts_with("modify_")
            || fn_lower.ends_with("_contract")
            || fn_lower.ends_with("_config")
        {
            return;
        }

        // Check if the method body asserts 1 yoctoNEAR (access-control pattern)
        if body_src.contains("assert_one_yocto")
            || body_src.contains("ONE_YOCTO")
            || body_src.contains("1_000_000_000_000_000_000_000_000")
        {
            return;
        }

        let line = span_to_line(&method.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "NEAR-010".to_string(),
            name: "missing-deposit-check".to_string(),
            severity: Severity::High,
            confidence: Confidence::High,
            message: format!(
                "#[payable] method '{}' does not check env::attached_deposit()",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&method.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add `let deposit = env::attached_deposit(); assert!(deposit > 0);` or validate deposit amount".to_string(),
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
        MissingDepositCheckDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_deposit_check() {
        let source = r#"
            use near_sdk::env;
            impl Contract {
                #[payable]
                pub fn purchase(&mut self, item_id: u64) {
                    self.inventory.remove(&item_id);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing deposit check");
    }

    #[test]
    fn test_no_finding_with_deposit_check() {
        let source = r#"
            use near_sdk::env;
            impl Contract {
                #[payable]
                pub fn purchase(&mut self, item_id: u64) {
                    let deposit = env::attached_deposit();
                    assert!(deposit >= self.prices.get(&item_id).unwrap());
                    self.inventory.remove(&item_id);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with deposit check");
    }

    // FP idx 0: deposit check factored into a private helper (resolved via call graph).
    #[test]
    fn test_no_finding_when_deposit_check_in_helper() {
        let source = r#"
            use near_sdk::{env, near_bindgen};

            #[near_bindgen]
            impl Marketplace {
                #[payable]
                pub fn purchase(&mut self, item_id: u64) {
                    self.assert_payment_covers(item_id);
                    self.inventory.remove(&item_id);
                }
            }

            impl Marketplace {
                fn assert_payment_covers(&self, item_id: u64) {
                    let price = self.prices.get(&item_id).unwrap();
                    assert!(env::attached_deposit() >= price, "insufficient deposit");
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a called helper validates the deposit"
        );
    }

    // FP idx 1: NEP-178 nft_revoke wrapper delegating to near_contract_standards.
    #[test]
    fn test_no_finding_for_nft_revoke_delegation() {
        let source = r#"
            use near_sdk::near_bindgen;

            #[near_bindgen]
            impl Contract {
                #[payable]
                pub fn nft_revoke(&mut self, token_id: TokenId, account_id: AccountId) {
                    self.tokens.nft_revoke(token_id, account_id)
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag standard nft_revoke delegating to the standards crate"
        );
    }

    // Soundness guard for FP idx 1: a hand-rolled nft_revoke that does NOT delegate
    // and does NOT check the deposit must still be flagged (no false negative).
    #[test]
    fn test_still_flags_hand_rolled_nft_revoke() {
        let source = r#"
            use near_sdk::near_bindgen;

            #[near_bindgen]
            impl Contract {
                #[payable]
                pub fn nft_revoke(&mut self, token_id: TokenId, account_id: AccountId) {
                    self.approvals.remove(&token_id);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag a hand-rolled nft_revoke with no yocto/deposit check"
        );
    }

    // FP idx 2: #[private] payable promise callback.
    #[test]
    fn test_no_finding_for_private_payable_callback() {
        let source = r#"
            use near_sdk::near_bindgen;

            #[near_bindgen]
            impl Contract {
                #[private]
                #[payable]
                pub fn on_refund_complete(&mut self, buyer: AccountId) {
                    self.pending_refunds.remove(&buyer);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a #[private] payable callback"
        );
    }

    // FP idx 3 (resolvable variant): custom one-yocto helper defined in the same file.
    #[test]
    fn test_no_finding_for_custom_one_yocto_helper_in_file() {
        let source = r#"
            use near_sdk::{near_bindgen, Promise};

            #[near_bindgen]
            impl Contract {
                #[payable]
                pub fn withdraw_all(&mut self) {
                    self.require_owner_one_yocto();
                    Promise::new(self.owner.clone()).transfer(self.balance);
                }

                fn require_owner_one_yocto(&self) {
                    assert_one_yocto();
                    assert_eq!(env::predecessor_account_id(), self.owner);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a resolved helper performs the 1-yocto assertion"
        );
    }

    // FP idx 4: payable methods on mock contracts inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_for_payable_in_cfg_test_module() {
        let source = r#"
            use near_sdk::near_bindgen;

            #[cfg(test)]
            mod tests {
                use super::*;

                #[near_bindgen]
                impl MockMarketplace {
                    #[payable]
                    pub fn purchase(&mut self, id: u64) {
                        self.calls += 1;
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag payable methods inside #[cfg(test)] modules"
        );
    }
}
