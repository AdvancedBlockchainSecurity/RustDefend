use quote::ToTokens;
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{Attribute, ItemFn, ItemMod, Meta, Token};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct Cw2MigrationDetector;

impl Detector for Cw2MigrationDetector {
    fn id(&self) -> &'static str {
        "CW-013"
    }
    fn name(&self) -> &'static str {
        "cw2-migration-issues"
    }
    fn description(&self) -> &'static str {
        "Detects cosmwasm-std 2.x API misuse patterns in migration code"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Skip if file doesn't contain cosmwasm markers or migrate
        if !ctx.source.contains("cosmwasm") && !ctx.source.contains("migrate") {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = MigrationVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const DEPRECATED_PATTERNS: &[(&str, &str)] = &[
    ("from_binary", "from_json"),
    ("to_binary", "to_json_binary"),
];

/// Returns true if this function is the CosmWasm migrate *entry point*
/// (named exactly `migrate`, or carrying an `entry_point` attribute — either
/// `#[entry_point]` or `#[cfg_attr(..., entry_point)]`). Per-version helper
/// functions named `migrate_*` are NOT entry points: they are state-transform
/// steps in the standard per-version-helper idiom, and the contract version is
/// stamped once by the entry point, so requiring each helper to re-stamp it
/// would be redundant and produce false positives.
fn fn_is_migrate_entry_point(func: &ItemFn) -> bool {
    if func.sig.ident == "migrate" {
        return true;
    }
    func.attrs
        .iter()
        .any(|attr| attr.to_token_stream().to_string().contains("entry_point"))
}

/// Returns true if the migrate body actually performs a migration: it mutates
/// storage (`.save`/`.update`/`.remove`) or has a success path (`Ok`).
///
/// A migrate entry point that performs no state mutation and cannot succeed —
/// e.g. an intentionally non-migratable stub that unconditionally returns
/// `Err(...)` — has no successful migration whose contract version could go
/// unrecorded, so it must not be flagged for a missing set_contract_version.
///
/// Note: `fn_body_source` returns a token-stream rendering (punctuation is
/// spaced out, but identifiers stay intact), so we match on the bare method /
/// variant idents. This intentionally errs toward returning `true`
/// (still-flag) so that no real missing-version bug is silently suppressed.
fn body_performs_migration(body_src: &str) -> bool {
    body_src.contains("save")
        || body_src.contains("update")
        || body_src.contains("remove")
        || body_src.contains("Ok")
}

/// Structurally evaluates a single `cfg` predicate and returns true only if the
/// predicate *requires* `test` to be enabled — i.e. the gated item cannot exist
/// in a non-test build.
///
/// The cfg predicate grammar (`test`, `all(..)`, `any(..)`, `not(..)`,
/// `feature = ".."`) maps exactly onto `syn::Meta`, so we walk it as an AST
/// rather than substring-matching the rendered tokens. Substring matching is
/// what made `#[cfg(not(test))]` — the *production* wasm gate — look test-only.
///
/// Errs toward returning false (descend and flag): a predicate we cannot prove
/// is test-exclusive is treated as production code, so no real bug is silently
/// suppressed.
fn cfg_requires_test(meta: &Meta) -> bool {
    match meta {
        // Bare `test`.
        Meta::Path(path) => path.is_ident("test"),
        // `feature = "testing"`, `target_os = "..."` — a cfg *option*, never
        // the `test` cfg itself, however its value happens to be spelled.
        Meta::NameValue(_) => false,
        Meta::List(list) => {
            let Ok(nested) = list.parse_args_with(Punctuated::<Meta, Token![,]>::parse_terminated)
            else {
                return false;
            };
            if list.path.is_ident("all") {
                // `all(test, ..)` holds only in test builds.
                nested.iter().any(cfg_requires_test)
            } else if list.path.is_ident("any") {
                // `any(test, feature = "x")` also holds in a non-test build
                // with `x` on, so it is test-exclusive only if every arm is.
                !nested.is_empty() && nested.iter().all(cfg_requires_test)
            } else {
                // `not(test)` is the production gate, and an unknown predicate
                // proves nothing. Neither is test-exclusive.
                false
            }
        }
    }
}

/// Returns true if these attributes gate the item to test builds only.
fn is_cfg_test_only(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if !attr.path().is_ident("cfg") {
            return false;
        }
        match attr.parse_args::<Meta>() {
            Ok(meta) => cfg_requires_test(&meta),
            Err(_) => false,
        }
    })
}

struct MigrationVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for MigrationVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Do not descend into test-only modules: their contents are never
        // compiled into the contract wasm, so test scaffolding (e.g. a
        // `migrate_*` setup helper) must not be flagged as production
        // migration code. The gate must be evaluated structurally — the
        // inverse gate `#[cfg(not(test))]` marks the *production* wasm
        // exports and must still be descended into.
        if is_cfg_test_only(&module.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Only check migrate entry points or migration-related functions
        if fn_name != "migrate" && !fn_name.starts_with("migrate_") {
            return;
        }

        // Skip test functions
        if has_attribute(&func.attrs, "test") {
            return;
        }

        let body_src = fn_body_source(func);

        // Check for deprecated API patterns
        for (deprecated, replacement) in DEPRECATED_PATTERNS {
            // Match the deprecated pattern but not if it's already the replacement
            let has_deprecated = body_src.contains(deprecated) && !body_src.contains(replacement);

            if has_deprecated {
                let line = span_to_line(&func.sig.ident.span());
                self.findings.push(Finding {
                    detector_id: "CW-013".to_string(),
                    name: "cw2-migration-issues".to_string(),
                    severity: Severity::Medium,
                    confidence: Confidence::Medium,
                    message: format!(
                        "Migrate function '{}' uses deprecated '{}' instead of '{}'",
                        fn_name, deprecated, replacement
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&func.sig.ident.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Update to cosmwasm-std 2.x API: use from_json/to_json_binary instead of from_binary/to_binary, and ensure set_contract_version is called in migrate".to_string(),
                    chain: Chain::CosmWasm,
                });
            }
        }

        // Check for missing set_contract_version call — only if the file
        // already uses cw2 (imports it or references it), indicating the project
        // uses versioned migrations. Otherwise this is too noisy.
        let file_uses_cw2 = self.ctx.source.contains("cw2")
            || self.ctx.source.contains("set_contract_version")
            || self.ctx.source.contains("get_contract_version")
            || self.ctx.source.contains("CONTRACT_VERSION");

        // The version stamp only needs to happen once, in the migrate entry
        // point. Per-version helper functions (`migrate_*`) delegate the stamp
        // to their caller, so we only run the missing-version check against the
        // actual entry point. A vulnerable entry point that never records the
        // version is still caught.
        if file_uses_cw2 && fn_is_migrate_entry_point(func) {
            let has_set_version = body_src.contains("set_contract_version")
                || body_src.contains("set _ contract _ version")
                // cw2::ensure_from_older_version validates the stored contract
                // name, rejects downgrades, and writes the new version itself
                // (it calls set_contract_version internally) — strictly stronger
                // than a bare set_contract_version call.
                || body_src.contains("ensure_from_older_version");

            // A migrate that performs no state mutation and cannot succeed
            // (an intentionally non-migratable Err stub) has no version to
            // record, so it is not a missing-version bug.
            let performs_migration = body_performs_migration(&body_src);

            if !has_set_version && performs_migration {
                let line = span_to_line(&func.sig.ident.span());
                self.findings.push(Finding {
                    detector_id: "CW-013".to_string(),
                    name: "cw2-migration-issues".to_string(),
                    severity: Severity::Medium,
                    confidence: Confidence::Low,
                    message: format!(
                        "Migrate function '{}' does not call cw2::set_contract_version",
                        fn_name
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&func.sig.ident.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Ensure set_contract_version is called in migrate to track contract versions across upgrades".to_string(),
                    chain: Chain::CosmWasm,
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
            Chain::CosmWasm,
            std::collections::HashMap::new(),
        );
        Cw2MigrationDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_deprecated_from_binary() {
        let source = r#"
            use cosmwasm_std::from_binary;
            #[entry_point]
            fn migrate(deps: DepsMut, env: Env, msg: MigrateMsg) -> StdResult<Response> {
                let data: OldState = from_binary(&msg.data)?;
                CONFIG.save(deps.storage, &data.into())?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect deprecated from_binary usage"
        );
        assert!(
            findings.iter().any(|f| f.message.contains("from_binary")),
            "Should mention from_binary in finding"
        );
    }

    #[test]
    fn test_no_finding_with_modern_api() {
        let source = r#"
            use cosmwasm_std::from_json;
            #[entry_point]
            fn migrate(deps: DepsMut, env: Env, msg: MigrateMsg) -> StdResult<Response> {
                let data: OldState = from_json(&msg.data)?;
                set_contract_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                CONFIG.save(deps.storage, &data.into())?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag modern cosmwasm-std 2.x API usage"
        );
    }

    // FP idx 0: per-version migrate_* helper flagged for a version already set
    // by the entry point.
    #[test]
    fn test_no_finding_migrate_helper_version_set_in_entry_point() {
        let source = r#"
            use cw2::set_contract_version;
            #[entry_point]
            pub fn migrate(deps: DepsMut, _env: Env, _msg: MigrateMsg) -> Result<Response, ContractError> {
                cw2::set_contract_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                migrate_v1_to_v2(deps)?;
                Ok(Response::new())
            }

            fn migrate_v1_to_v2(deps: DepsMut) -> Result<(), ContractError> {
                let old = OLD_CONFIG.load(deps.storage)?;
                CONFIG.save(deps.storage, &old.into())?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "migrate_* helper must not be flagged when the entry point sets the version"
        );
    }

    // FP idx 2: cw2::ensure_from_older_version writes the version internally.
    #[test]
    fn test_no_finding_ensure_from_older_version() {
        let source = r#"
            use cw2::ensure_from_older_version;
            #[entry_point]
            pub fn migrate(deps: DepsMut, _env: Env, _msg: MigrateMsg) -> Result<Response, ContractError> {
                ensure_from_older_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "ensure_from_older_version records the version; should not be flagged"
        );
    }

    // FP idx 3: intentionally non-migratable stub that always returns Err.
    #[test]
    fn test_no_finding_non_migratable_err_stub() {
        let source = r#"
            use cw2::set_contract_version;
            #[entry_point]
            pub fn instantiate(deps: DepsMut, _env: Env, _info: MessageInfo, _msg: InstantiateMsg) -> Result<Response, ContractError> {
                cw2::set_contract_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                Ok(Response::new())
            }
            #[entry_point]
            pub fn migrate(_deps: DepsMut, _env: Env, _msg: MigrateMsg) -> Result<Response, ContractError> {
                Err(ContractError::MigrationNotSupported {})
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A migrate stub that unconditionally returns Err must not be flagged for missing set_contract_version"
        );
    }

    // FP idx 4: migrate_* helper inside a #[cfg(test)] module is test
    // scaffolding, never compiled into the wasm.
    #[test]
    fn test_no_finding_migrate_helper_in_cfg_test_module() {
        let source = r#"
            use cw2::set_contract_version;
            #[entry_point]
            pub fn migrate(deps: DepsMut, _env: Env, _msg: MigrateMsg) -> Result<Response, ContractError> {
                cw2::set_contract_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                Ok(Response::new())
            }

            #[cfg(test)]
            mod tests {
                use super::*;

                fn migrate_with(deps: DepsMut, raw: &Binary) -> StdResult<Response> {
                    let msg: MigrateMsg = from_binary(raw)?;
                    migrate(deps, mock_env(), msg)
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "migrate_* helper inside a #[cfg(test)] module must not be flagged"
        );
    }

    // Must-still-fire: `#[cfg(not(test))]` is the *production* wasm-export
    // gate, the exact inverse of `#[cfg(test)]`. A migrate entry point inside
    // it uses the deprecated from_binary API and never records the contract
    // version — both real bugs, in code that ships in the wasm.
    #[test]
    fn test_still_flags_migrate_in_cfg_not_test_module() {
        let source = r#"
            use cosmwasm_std::{entry_point, from_binary, DepsMut, Env, Response, StdResult};
            use cw2::{get_contract_version, set_contract_version};

            #[cfg(not(test))]
            mod entry {
                use super::*;

                #[entry_point]
                pub fn migrate(deps: DepsMut, _env: Env, msg: MigrateMsg) -> StdResult<Response> {
                    let incoming: Config = from_binary(&msg.data)?;
                    CONFIG.save(deps.storage, &incoming)?;
                    Ok(Response::new().add_attribute("action", "migrate"))
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.message.contains("from_binary")),
            "migrate inside a #[cfg(not(test))] production module must still be flagged for from_binary"
        );
        assert!(
            findings
                .iter()
                .any(|f| f.message.contains("set_contract_version")),
            "migrate inside a #[cfg(not(test))] production module must still be flagged for the missing version stamp"
        );
    }

    // The test-only skip must survive under composite predicates that still
    // require `test`, while inverse/disjunctive gates stay in scope.
    #[test]
    fn test_still_flags_migrate_in_any_test_or_feature_module() {
        let source = r#"
            use cw2::set_contract_version;

            // Compiled into the wasm whenever `debug-tools` is on, so this is
            // not test-exclusive scaffolding.
            #[cfg(any(test, feature = "debug-tools"))]
            mod tools {
                use super::*;

                #[entry_point]
                pub fn migrate(deps: DepsMut, _env: Env, msg: MigrateMsg) -> StdResult<Response> {
                    let incoming: Config = from_binary(&msg.data)?;
                    CONFIG.save(deps.storage, &incoming)?;
                    Ok(Response::new())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.message.contains("from_binary")),
            "a module gated on any(test, feature = ..) can ship in the wasm and must still be flagged"
        );
    }

    // Composite gate that genuinely requires `test`: still scaffolding.
    #[test]
    fn test_no_finding_migrate_helper_in_all_test_module() {
        let source = r#"
            use cw2::set_contract_version;
            #[entry_point]
            pub fn migrate(deps: DepsMut, _env: Env, _msg: MigrateMsg) -> Result<Response, ContractError> {
                cw2::set_contract_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                Ok(Response::new())
            }

            #[cfg(all(test, not(target_arch = "wasm32")))]
            mod tests {
                use super::*;

                fn migrate_with(deps: DepsMut, raw: &Binary) -> StdResult<Response> {
                    let msg: MigrateMsg = from_binary(raw)?;
                    migrate(deps, mock_env(), msg)
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "a module gated on all(test, ..) is test-only scaffolding and must not be flagged"
        );
    }

    // Must-still-fire: an entry-point migrate that mutates state and returns Ok
    // but never records the contract version is a real bug.
    #[test]
    fn test_still_flags_entry_point_missing_version() {
        let source = r#"
            use cw2::set_contract_version;
            #[entry_point]
            pub fn migrate(deps: DepsMut, _env: Env, _msg: MigrateMsg) -> Result<Response, ContractError> {
                let old = OLD_CONFIG.load(deps.storage)?;
                CONFIG.save(deps.storage, &old.into())?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.message.contains("set_contract_version")),
            "Entry-point migrate that mutates state without recording the version must still be flagged"
        );
    }
}
