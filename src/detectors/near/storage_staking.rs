use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{
    Attribute, Block, Expr, ExprCall, ExprMethodCall, ExprPath, FnArg, ItemFn, ItemMod, Signature,
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
        // Build a within-file map of every (non-test) function/method body and the
        // set of callees each invokes. This lets us soundly resolve whether the
        // caller identity is authorized one frame up (a trusted caller that reads
        // `predecessor_account_id` and passes the account down) or one frame down
        // (auth factored into a shared helper), instead of relying on a single
        // literal match on the flagged function's own body.
        let mut collector = FnDefCollector {
            bodies: HashMap::new(),
            calls: HashMap::new(),
        };
        collector.visit_file(&ctx.ast);

        let mut findings = Vec::new();
        let mut visitor = StorageVisitor {
            findings: &mut findings,
            ctx,
            bodies: &collector.bodies,
            calls: &collector.calls,
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

/// Visitor that records, for each non-test function/method in the file, its body
/// source and the callees it invokes.
struct FnDefCollector {
    bodies: HashMap<String, String>,
    calls: HashMap<String, Vec<String>>,
}

impl FnDefCollector {
    fn record(&mut self, name: String, block: &Block) {
        self.bodies
            .insert(name.clone(), block.to_token_stream().to_string());
        self.calls.insert(name, collect_callees_block(block));
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
            self.record(func.sig.ident.to_string(), &func.block);
        }
        syn::visit::visit_item_fn(self, func);
    }

    fn visit_impl_item_fn(&mut self, func: &'ast syn::ImplItemFn) {
        if !is_test_fn(&func.attrs) {
            self.record(func.sig.ident.to_string(), &func.block);
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
    bodies: &'a HashMap<String, String>,
    calls: &'a HashMap<String, Vec<String>>,
}

impl<'a> StorageVisitor<'a> {
    /// Authorization delegated *down*: the flagged function calls a same-file
    /// helper whose own body resolves `predecessor_account_id` (idiomatic
    /// `assert_registered_caller()` / `assert_owner()` factoring).
    fn auth_in_callees(&self, func: &ItemFn) -> bool {
        collect_callees_block(&func.block).iter().any(|callee| {
            self.bodies
                .get(callee)
                .is_some_and(|body| body.contains("predecessor_account_id"))
        })
    }

    /// Authorization delegated *up*: a trusted same-file caller invokes this
    /// function and performs the `predecessor_account_id` check itself, passing
    /// the resolved account identity down (the NEP-145 public/internal layering).
    fn auth_in_callers(&self, fn_name: &str) -> bool {
        self.calls.iter().any(|(caller, callees)| {
            caller != fn_name
                && callees.iter().any(|c| c == fn_name)
                && self
                    .bodies
                    .get(caller)
                    .is_some_and(|body| body.contains("predecessor_account_id"))
        })
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
