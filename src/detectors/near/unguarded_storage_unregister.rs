use std::collections::HashMap;

use syn::visit::Visit;
use syn::{Attribute, Expr, ExprCall, ItemFn};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnguardedStorageUnregisterDetector;

impl Detector for UnguardedStorageUnregisterDetector {
    fn id(&self) -> &'static str {
        "NEAR-011"
    }
    fn name(&self) -> &'static str {
        "unguarded-storage-unregister"
    }
    fn description(&self) -> &'static str {
        "Detects storage_unregister without checking non-zero token balances"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Near
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Integration-test files (tests/**) never ship in the contract wasm and
        // cannot destroy on-chain user funds; skip them entirely.
        if ctx.file_path.to_string_lossy().contains("/tests/") {
            return Vec::new();
        }

        let mut findings = Vec::new();
        // Pre-resolve production (non-#[cfg(test)]) free functions so we can see
        // balance checks that were factored into a callee or performed by an
        // enclosing caller instead of being inlined into the flagged body.
        let prod_fns = collect_prod_fns(&ctx.ast);
        let mut visitor = StorageUnregisterVisitor {
            findings: &mut findings,
            ctx,
            prod_fns: &prod_fns,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const BALANCE_CHECK_PATTERNS: &[&str] = &[
    "balance",
    "amount",
    "is_empty",
    "== 0",
    "!= 0",
    "> 0",
    "is_zero",
    "non_zero",
    "nonzero",
    "has_balance",
    "tokens",
    "force",
];

/// A resolved production free function: its body token-source and the names of
/// the functions it calls.
struct ProdFn {
    body: String,
    calls: Vec<String>,
}

/// Collect production (non-`#[cfg(test)]`) free functions keyed by name. Test
/// modules are never descended into, so test scaffolding can never be used to
/// suppress a finding on real contract code.
fn collect_prod_fns(file: &syn::File) -> HashMap<String, ProdFn> {
    let mut map = HashMap::new();
    collect_prod_fns_items(&file.items, &mut map);
    map
}

fn collect_prod_fns_items(items: &[syn::Item], map: &mut HashMap<String, ProdFn>) {
    for item in items {
        match item {
            syn::Item::Fn(f) => {
                map.insert(
                    f.sig.ident.to_string(),
                    ProdFn {
                        body: fn_body_source(f),
                        calls: collect_call_names(f),
                    },
                );
            }
            syn::Item::Mod(m) => {
                // Never descend into test-only modules.
                if has_attribute_with_value(&m.attrs, "cfg", "test") {
                    continue;
                }
                if let Some((_, inner)) = &m.content {
                    collect_prod_fns_items(inner, map);
                }
            }
            _ => {}
        }
    }
}

/// Collect the names of free functions called (via path call expressions) inside
/// a function body. Method calls (e.g. `map.remove(..)`) are intentionally not
/// resolved as callees.
fn collect_call_names(func: &ItemFn) -> Vec<String> {
    struct CallNameCollector {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for CallNameCollector {
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Expr::Path(p) = node.func.as_ref() {
                if let Some(seg) = p.path.segments.last() {
                    self.names.push(seg.ident.to_string());
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }
    let mut c = CallNameCollector { names: Vec::new() };
    c.visit_item_fn(func);
    c.names
}

fn body_has_balance_check(body: &str) -> bool {
    BALANCE_CHECK_PATTERNS.iter().any(|p| body.contains(p))
}

/// Whether a body actually removes/unregisters an account. Token-stream source
/// renders `.remove(` / `storage_remove` / `.swap_remove(` all containing the
/// `remove` identifier, so a single substring test covers them.
fn body_removes(body: &str) -> bool {
    body.contains("remove")
}

/// Test-function attributes across the common frameworks.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    has_attribute(attrs, "test")
        || has_attribute(attrs, "tokio::test")
        || has_attribute(attrs, "ink::test")
}

struct StorageUnregisterVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    prod_fns: &'a HashMap<String, ProdFn>,
}

impl<'a> StorageUnregisterVisitor<'a> {
    /// True if the flagged function removes something directly, or delegates the
    /// removal to a resolvable callee that removes. Pure event emitters /
    /// predicates that mutate no storage return false.
    fn removes_something(&self, body_src: &str, callees: &[String]) -> bool {
        if body_removes(body_src) {
            return true;
        }
        callees
            .iter()
            .filter_map(|c| self.prod_fns.get(c))
            .any(|pf| body_removes(&pf.body))
    }

    /// True if a resolvable callee performs the non-zero-balance check (the
    /// guard was factored into a helper).
    fn callee_checks_balance(&self, callees: &[String]) -> bool {
        callees
            .iter()
            .filter_map(|c| self.prod_fns.get(c))
            .any(|pf| body_has_balance_check(&pf.body))
    }

    /// True if the function has at least one in-file caller and every such
    /// caller performs the balance check before delegating. With no callers
    /// (e.g. a public entry point) this returns false so the finding stands.
    fn all_callers_check_balance(&self, fn_name: &str) -> bool {
        let mut had_caller = false;
        for (name, pf) in self.prod_fns.iter() {
            if name == fn_name {
                continue;
            }
            if pf.calls.iter().any(|c| c == fn_name) {
                had_caller = true;
                if !body_has_balance_check(&pf.body) {
                    return false;
                }
            }
        }
        had_caller
    }
}

impl<'ast, 'a> Visit<'ast> for StorageUnregisterVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        // Do not analyze code compiled only under #[cfg(test)] — it never ships
        // in the deployed wasm and cannot destroy user funds.
        if has_attribute_with_value(&node.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        if !fn_name.contains("storage_unregister") {
            return;
        }

        // Skip test functions.
        if fn_name.starts_with("test_") || fn_name.ends_with("_test") || is_test_fn(&func.attrs) {
            return;
        }

        let body_src = fn_body_source(func);
        let callees = collect_call_names(func);

        // The function must actually remove/unregister an account (directly or
        // via a resolvable callee). Pure log/event emitters and predicates that
        // merely share the `storage_unregister` substring have no balance to
        // guard and are not a hazard.
        if !self.removes_something(&body_src, &callees) {
            return;
        }

        // Guard is inlined in this body.
        if body_has_balance_check(&body_src) {
            return;
        }

        // Guard is factored into a resolvable callee (check-in-helper).
        if self.callee_checks_balance(&callees) {
            return;
        }

        // Guard is enforced by every in-file caller before delegating here
        // (check-at-boundary, act-in-helper).
        if self.all_callers_check_balance(&fn_name) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "NEAR-011".to_string(),
            name: "unguarded-storage-unregister".to_string(),
            severity: Severity::Medium,
            confidence: Confidence::Medium,
            message: format!(
                "Storage unregister handler '{}' does not check for non-zero token balances before removing account",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Check that the account has zero token balance before allowing storage_unregister, or require a 'force' parameter to acknowledge token loss".to_string(),
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
        UnguardedStorageUnregisterDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unguarded_unregister() {
        let source = r#"
            fn storage_unregister(&mut self) -> bool {
                let account_id = env::predecessor_account_id();
                self.accounts.remove(&account_id);
                env::storage_remove(&account_id.as_bytes());
                true
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect unguarded storage_unregister"
        );
        assert_eq!(findings[0].detector_id, "NEAR-011");
    }

    #[test]
    fn test_no_finding_with_balance_check() {
        let source = r#"
            fn storage_unregister(&mut self, force: Option<bool>) -> bool {
                let account_id = env::predecessor_account_id();
                let balance = self.internal_unwrap_balance_of(&account_id);
                if balance != 0 && !force.unwrap_or(false) {
                    env::panic_str("account has non-zero balance, use force=true to unregister");
                }
                self.accounts.remove(&account_id);
                true
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with balance check");
    }

    #[test]
    fn test_no_finding_with_force_param() {
        let source = r#"
            fn storage_unregister(&mut self, force: Option<bool>) -> bool {
                let account_id = env::predecessor_account_id();
                if !force.unwrap_or(false) {
                    return false;
                }
                self.accounts.remove(&account_id);
                true
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when force parameter is checked"
        );
    }

    // FP idx 0: balance check factored into a resolvable callee whose name
    // matches no pattern.
    #[test]
    fn test_no_finding_when_callee_checks_balance() {
        let source = r#"
            pub fn storage_unregister_account(state: &mut Contract, account_id: &AccountId) -> bool {
                assert_account_empty(state, account_id);
                state.accounts.remove(account_id);
                true
            }

            fn assert_account_empty(state: &Contract, account_id: &AccountId) {
                assert!(state.balance_of(account_id) == 0, "account not empty");
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a resolved callee performs the balance check"
        );
    }

    // FP idx 1: test scaffolding inside a #[cfg(test)] module, not annotated
    // #[test] and not named test_*.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;

                fn do_storage_unregister(contract: &mut Contract) -> bool {
                    testing_env!(get_context(accounts(1)));
                    contract.accounts.remove(&accounts(1));
                    contract.storage_unregister(None)
                }

                #[test]
                fn test_unregister_flow() {
                    let mut contract = Contract::default();
                    do_storage_unregister(&mut contract);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag test scaffolding inside a #[cfg(test)] module"
        );
    }

    // FP idx 2: name-substring match on a function that removes nothing (pure
    // event emitter).
    #[test]
    fn test_no_finding_for_event_emitter() {
        let source = r#"
            fn emit_storage_unregister(account_id: &AccountId) {
                env::log_str(&format!("EVENT_JSON: storage_unregister {}", account_id));
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a function that removes/mutates nothing"
        );
    }

    // FP idx 3: private _unchecked helper whose sole in-file caller enforces the
    // balance check before delegating.
    #[test]
    fn test_no_finding_for_unchecked_helper_guarded_by_caller() {
        let source = r#"
            fn storage_unregister_unchecked(contract: &mut Contract, account_id: &AccountId) {
                contract.accounts.remove(account_id);
            }

            pub fn storage_unregister(contract: &mut Contract, force: Option<bool>) -> bool {
                let balance = contract.internal_balance_of(&env::predecessor_account_id());
                assert!(balance == 0 || force.unwrap_or(false), "non-zero balance");
                storage_unregister_unchecked(contract, &env::predecessor_account_id());
                true
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag an _unchecked helper whose only caller checks the balance"
        );
    }

    // Guard-narrowing sanity check: a delegating unregister whose helper removes
    // but where NO caller checks the balance must still fire (no false negative
    // from the mutation / caller guards).
    #[test]
    fn test_still_detects_delegated_removal_without_check() {
        let source = r#"
            fn remove_account(contract: &mut Contract, account_id: &AccountId) {
                contract.accounts.remove(account_id);
            }

            pub fn storage_unregister(contract: &mut Contract) -> bool {
                let account_id = env::predecessor_account_id();
                remove_account(contract, &account_id);
                true
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still detect a delegated removal with no balance check anywhere"
        );
    }
}
