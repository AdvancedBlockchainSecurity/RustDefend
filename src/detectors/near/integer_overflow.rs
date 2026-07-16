use quote::ToTokens;
use syn::visit::Visit;
use syn::{ExprMethodCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct IntegerOverflowDetector;

impl Detector for IntegerOverflowDetector {
    fn id(&self) -> &'static str {
        "NEAR-005"
    }
    fn name(&self) -> &'static str {
        "near-wrapping-arithmetic"
    }
    fn description(&self) -> &'static str {
        "Detects wrapping_*/saturating_* on balance/amount variables"
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
        let mut visitor = OverflowVisitor {
            findings: &mut findings,
            ctx,
            in_function: false,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct OverflowVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    in_function: bool,
}

/// A `cfg(...)` predicate, modelled structurally. Atoms other than a bare
/// `test` (`feature = "x"`, `target_os = "wasm32"`, ...) are not interpreted:
/// they are `Unknown` and may take either value.
enum CfgPred {
    /// The bare `test` atom, i.e. the flag rustc sets only for test builds.
    Test,
    /// Any atom we do not model; free to be either true or false.
    Unknown,
    Not(Box<CfgPred>),
    All(Vec<CfgPred>),
    Any(Vec<CfgPred>),
}

/// Lowers a `cfg` predicate's `Meta` into a `CfgPred` tree.
fn parse_cfg_pred(meta: &syn::Meta) -> CfgPred {
    match meta {
        syn::Meta::Path(path) => {
            if path.is_ident("test") {
                CfgPred::Test
            } else {
                CfgPred::Unknown
            }
        }
        syn::Meta::List(list) => {
            let nested = match list.parse_args_with(
                syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
            ) {
                Ok(nested) => nested,
                // Unparsable predicate: assume nothing about it.
                Err(_) => return CfgPred::Unknown,
            };
            let mut children: Vec<CfgPred> = nested.iter().map(parse_cfg_pred).collect();
            if list.path.is_ident("not") {
                // `not` takes exactly one predicate.
                match children.pop() {
                    Some(child) if children.is_empty() => CfgPred::Not(Box::new(child)),
                    _ => CfgPred::Unknown,
                }
            } else if list.path.is_ident("all") {
                CfgPred::All(children)
            } else if list.path.is_ident("any") {
                CfgPred::Any(children)
            } else {
                // e.g. `feature("x")` style atoms we do not model.
                CfgPred::Unknown
            }
        }
        // `feature = "x"`, `target_os = "linux"`, ...
        syn::Meta::NameValue(_) => CfgPred::Unknown,
    }
}

/// Can this predicate hold in a build where `test` is NOT set (i.e. the
/// release WASM build)? Unknown atoms are free, so this asks whether *some*
/// non-test configuration compiles the item in.
fn can_hold_without_test(pred: &CfgPred) -> bool {
    match pred {
        CfgPred::Test => false,
        CfgPred::Unknown => true,
        CfgPred::Not(inner) => can_fail_without_test(inner),
        CfgPred::All(children) => children.iter().all(can_hold_without_test),
        CfgPred::Any(children) => children.iter().any(can_hold_without_test),
    }
}

/// Dual of `can_hold_without_test`: can this predicate be false in a build
/// where `test` is not set? Needed to push negations through `not(...)`.
fn can_fail_without_test(pred: &CfgPred) -> bool {
    match pred {
        CfgPred::Test => true,
        CfgPred::Unknown => true,
        CfgPred::Not(inner) => can_hold_without_test(inner),
        CfgPred::All(children) => children.iter().any(can_fail_without_test),
        CfgPred::Any(children) => children.iter().all(can_fail_without_test),
    }
}

/// Returns true if the attributes mark this item as test-only code, i.e.
/// `#[cfg(test)]`, `#[test]`, or a framework test attribute
/// (`#[tokio::test]`, `#[ink::test]`, `#[near_sdk::test]`, ...). Such code is
/// excluded from the release WASM build and never executes on-chain, so
/// intentional overflow edge-case exercises there are not deployable
/// vulnerabilities.
///
/// The `cfg` predicate is *evaluated* rather than string-matched: an item is
/// test-only only when no non-test configuration can compile it in. A raw
/// `contains("test")` check would misread `#[cfg(not(test))]` -- production-
/// only code, the exact opposite -- as test-only and silently drop real
/// findings on the deployed path.
fn is_test_only(attrs: &[syn::Attribute]) -> bool {
    // Multiple `#[cfg(..)]` attributes on one item are ANDed, so any single
    // predicate that excludes every non-test build makes the item test-only.
    let cfg_test_only = attrs.iter().any(|attr| {
        if !attr.path().is_ident("cfg") {
            return false;
        }
        let list = match &attr.meta {
            syn::Meta::List(list) => list,
            _ => return false,
        };
        let nested = match list.parse_args_with(
            syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated,
        ) {
            Ok(nested) => nested,
            Err(_) => return false,
        };
        // `cfg` takes exactly one predicate.
        match nested.first() {
            Some(meta) if nested.len() == 1 => !can_hold_without_test(&parse_cfg_pred(meta)),
            _ => false,
        }
    });
    if cfg_test_only {
        return true;
    }
    attrs.iter().any(|attr| {
        // Match the last path segment so that plain `#[test]` as well as
        // `#[tokio::test]`, `#[ink::test]`, `#[near_sdk::test]`, etc. are all
        // treated as test attributes.
        attr.path()
            .segments
            .last()
            .map(|seg| seg.ident == "test")
            .unwrap_or(false)
    })
}

impl<'ast, 'a> Visit<'ast> for OverflowVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Do not descend into test-only modules (`#[cfg(test)] mod tests`).
        // Their arithmetic is compiled out of the deployed contract and often
        // intentionally exercises overflow edge cases.
        if is_test_only(&module.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (`#[test]`, `#[tokio::test]`, `#[ink::test]`,
        // `#[cfg(test)] fn ...`) even if they are not inside a test module.
        if is_test_only(&func.attrs) {
            return;
        }
        self.in_function = true;
        syn::visit::visit_item_fn(self, func);
        self.in_function = false;
    }

    fn visit_expr_method_call(&mut self, call: &'ast ExprMethodCall) {
        if !self.in_function {
            syn::visit::visit_expr_method_call(self, call);
            return;
        }

        let method = call.method.to_string();

        // Flag wrapping_* and saturating_* operations on financial values
        if method.starts_with("wrapping_") || method.starts_with("saturating_") {
            let expr_str = call.to_token_stream().to_string();

            // Check if this involves balance/amount/token related variables
            let is_financial = expr_str.contains("balance")
                || expr_str.contains("amount")
                || expr_str.contains("deposit")
                || expr_str.contains("stake")
                || expr_str.contains("token")
                || expr_str.contains("reward");

            if is_financial {
                let line = span_to_line(&call.method.span());
                self.findings.push(Finding {
                    detector_id: "NEAR-005".to_string(),
                    name: "near-wrapping-arithmetic".to_string(),
                    severity: Severity::Critical,
                    confidence: Confidence::Medium,
                    message: format!(
                        "{}() used on financial value - may silently lose precision",
                        method
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&call.method.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Use checked_* arithmetic and handle overflow explicitly for financial calculations".to_string(),
                    chain: Chain::Near,
                });
            }
        }

        syn::visit::visit_expr_method_call(self, call);
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
        IntegerOverflowDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_wrapping_on_balance() {
        let source = r#"
            use near_sdk::env;
            fn update_balance(&mut self, amount: u128) {
                self.balance = self.balance.wrapping_add(amount);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect wrapping_add on balance"
        );
    }

    #[test]
    fn test_no_finding_checked() {
        let source = r#"
            use near_sdk::env;
            fn update_balance(&mut self, amount: u128) -> Option<u128> {
                self.balance.checked_add(amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag checked_add");
    }

    #[test]
    fn test_no_finding_in_cfg_test_module() {
        // FP idx 4: wrapping_add inside a #[cfg(test)] module is test-only
        // code (compiled out of the deployed WASM) that intentionally
        // exercises the overflow edge case. It must not be flagged.
        let source = r#"
            use near_sdk::env;

            #[cfg(test)]
            mod tests {
                #[test]
                fn balance_wraps_at_u128_max_is_rejected() {
                    let balance: u128 = u128::MAX;
                    let wrapped = balance.wrapping_add(1);
                    assert_eq!(wrapped, 0);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag wrapping_add inside #[cfg(test)] module"
        );
    }

    #[test]
    fn test_no_finding_in_test_fn() {
        // A #[test] function not wrapped in a #[cfg(test)] module is still
        // test-only code and must not be flagged.
        let source = r#"
            use near_sdk::env;

            #[test]
            fn balance_overflow_case() {
                let balance: u128 = u128::MAX;
                let _ = balance.wrapping_add(1);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag wrapping_add inside a #[test] fn"
        );
    }

    #[test]
    fn test_still_flags_cfg_not_test_production_fn() {
        // REGRESSION (false negative): `#[cfg(not(test))]` marks code that
        // ships in the release WASM and is compiled OUT of test builds -- the
        // exact opposite of test-only. A substring `contains("test")` check on
        // the stringified cfg attribute silenced this genuinely vulnerable
        // on-chain debit path. Must always be flagged.
        let source = r#"
            use near_sdk::{env, near_bindgen, AccountId, Balance};

            #[cfg(not(test))]
            fn debit_stake(pool: &mut StakingPool, account: &AccountId, amount: Balance) -> Balance {
                let current = pool.staked.get(account).unwrap_or(0);
                let remaining = current.wrapping_sub(amount);
                pool.staked.insert(account, &remaining);
                pool.total_staked = pool.total_staked.wrapping_sub(amount);
                remaining
            }

            #[cfg(test)]
            fn debit_stake(pool: &mut StakingPool, account: &AccountId, amount: Balance) -> Balance {
                let current = pool.staked.get(account).unwrap_or(0);
                let remaining = current.checked_sub(amount).expect("insufficient stake");
                pool.staked.insert(account, &remaining);
                pool.total_staked = pool.total_staked.checked_sub(amount).expect("underflow");
                remaining
            }
        "#;
        let findings = run_detector(source);
        assert_eq!(
            findings.len(),
            2,
            "Should flag both wrapping_sub calls in the #[cfg(not(test))] production fn, got {:?}",
            findings
        );
    }

    #[test]
    fn test_still_flags_cfg_any_test_or_feature() {
        // `any(test, feature = "x")` still compiles in a non-test build when
        // the feature is enabled, so it is not test-only.
        let source = r#"
            use near_sdk::env;

            #[cfg(any(test, feature = "simulation"))]
            fn debit(balance: u128, amount: u128) -> u128 {
                balance.wrapping_sub(amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag wrapping_sub under #[cfg(any(test, feature = ...))]"
        );
    }

    #[test]
    fn test_no_finding_cfg_all_test_and_feature() {
        // `all(test, feature = "x")` cannot hold in any non-test build, so it
        // is test-only and must stay silent.
        let source = r#"
            use near_sdk::env;

            #[cfg(all(test, feature = "simulation"))]
            fn balance_wraps(balance: u128, amount: u128) -> u128 {
                balance.wrapping_sub(amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag wrapping_sub under #[cfg(all(test, feature = ...))]"
        );
    }

    #[test]
    fn test_still_flags_cfg_feature_gated_fn() {
        // A plain feature gate is not a test gate.
        let source = r#"
            use near_sdk::env;

            #[cfg(not(feature = "stub"))]
            fn debit(balance: u128, amount: u128) -> u128 {
                balance.wrapping_sub(amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag wrapping_sub under a non-test feature gate"
        );
    }
}
