use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Expr, ExprCall, FnArg, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnguardedMigrateDetector;

impl Detector for UnguardedMigrateDetector {
    fn id(&self) -> &'static str {
        "CW-010"
    }
    fn name(&self) -> &'static str {
        "unguarded-migrate-entry"
    }
    fn description(&self) -> &'static str {
        "Detects migrate handler without admin/sender check or version validation"
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
        let mut findings = Vec::new();

        // Build a lightweight index of every top-level function in the file so we can
        // resolve callee/caller guard propagation without touching shared infra.
        let mut collector = FunctionCollector { functions: vec![] };
        collector.visit_file(&ctx.ast);
        let mut fn_index: HashMap<String, FnMeta> = HashMap::new();
        for func in &collector.functions {
            let name = func.sig.ident.to_string();
            let body = fn_body_source(func);
            let guarded = body_is_guarded(&body);
            let calls = collect_called_names(func);
            // Last definition wins on name collision; acceptable for a heuristic index.
            fn_index.insert(name, FnMeta { calls, guarded });
        }

        let mut visitor = MigrateVisitor {
            findings: &mut findings,
            ctx,
            fn_index: &fn_index,
            in_test_module: false,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const AUTH_PATTERNS: &[&str] = &[
    "info . sender",
    "info.sender",
    "sender",
    "admin",
    "owner",
    "ADMIN",
    "OWNER",
    "is_admin",
    "is_owner",
    "only_admin",
    "only_owner",
    "ensure_admin",
];

const VERSION_PATTERNS: &[&str] = &[
    "version",
    "VERSION",
    "get_contract_version",
    "set_contract_version",
    "cw2 ::",
    "migrate_version",
    "assert_contract_version",
    "ensure_from_older_version",
];

/// True if a function body contains an admin/sender check or a version validation.
fn body_is_guarded(body: &str) -> bool {
    AUTH_PATTERNS.iter().any(|p| body.contains(p))
        || VERSION_PATTERNS.iter().any(|p| body.contains(p))
}

/// Minimal per-function metadata used for guard propagation.
struct FnMeta {
    /// Names of directly-called functions (last path segment of each call expr).
    calls: Vec<String>,
    /// Whether this function's own body contains an auth or version guard.
    guarded: bool,
}

/// Collect the names of functions called directly from `func`'s body.
/// Only call expressions (`foo(..)`, `a::b::foo(..)`) are recorded — the last
/// path segment — which is what we need to resolve local helper calls.
fn collect_called_names(func: &ItemFn) -> Vec<String> {
    struct CalledNames {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for CalledNames {
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Expr::Path(p) = node.func.as_ref() {
                if let Some(seg) = p.path.segments.last() {
                    let name = seg.ident.to_string();
                    if !self.names.contains(&name) {
                        self.names.push(name);
                    }
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }
    let mut c = CalledNames { names: vec![] };
    c.visit_block(&func.block);
    c.names
}

/// Whether a function looks like it could actually be a CosmWasm migrate entry
/// point: it either carries an `entry_point` attribute (including inside a
/// `cfg_attr`), or its signature takes a `DepsMut` / `&mut dyn Storage` argument.
/// Pure data converters (e.g. `fn migrate_config(old: ConfigV1) -> ConfigV2`)
/// fail both tests and are therefore not migration handlers. Genuine unguarded
/// migrate entries always take `DepsMut`, so no true positive is lost.
fn looks_like_migrate_entry(func: &ItemFn) -> bool {
    // entry_point attribute, possibly wrapped in cfg_attr(..)
    if func
        .attrs
        .iter()
        .any(|a| a.to_token_stream().to_string().contains("entry_point"))
    {
        return true;
    }
    // signature touches contract storage
    func.sig.inputs.iter().any(|arg| {
        if let FnArg::Typed(pat) = arg {
            let ty = pat.ty.to_token_stream().to_string();
            ty.contains("DepsMut") || ty.contains("Storage")
        } else {
            false
        }
    })
}

/// True if any attribute is a test attribute: `#[test]`, `#[tokio::test]`,
/// `#[ink::test]`, etc. (matched on the final path segment).
fn is_test_attr(func: &ItemFn) -> bool {
    func.attrs.iter().any(|a| {
        a.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

/// True if any attribute is `#[cfg(test)]` (or another cfg gating on `test`).
fn attrs_have_cfg_test(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|a| {
        a.path().is_ident("cfg") && a.meta.to_token_stream().to_string().contains("test")
    })
}

struct MigrateVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    fn_index: &'a HashMap<String, FnMeta>,
    in_test_module: bool,
}

impl<'a> MigrateVisitor<'a> {
    /// One-level callee propagation: if the migrate body delegates to local
    /// helpers and *every* resolvable local callee is itself guarded, the
    /// migrate is effectively guarded (idiomatic dispatch pattern). If any
    /// resolvable local callee lacks a guard, the migrate stays flagged, so a
    /// genuinely unguarded arm is never suppressed.
    fn guarded_by_callees(&self, func: &ItemFn) -> bool {
        let calls = collect_called_names(func);
        let local: Vec<&String> = calls
            .iter()
            .filter(|n| self.fn_index.contains_key(*n))
            .collect();
        !local.is_empty() && local.iter().all(|n| self.fn_index[*n].guarded)
    }

    /// True if some function in the file calls `target` and is itself guarded.
    /// Used for private `migrate_*` helpers whose guard lives in the caller
    /// (the real entry point). A helper with no guarded caller stays flagged.
    fn any_caller_guarded(&self, target: &str) -> bool {
        self.fn_index
            .values()
            .any(|m| m.guarded && m.calls.iter().any(|c| c == target))
    }
}

impl<'ast, 'a> Visit<'ast> for MigrateVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Track whether we are inside a `#[cfg(test)]` module. Migrate handlers
        // defined there are cw-multi-test fixtures, never deployed on-chain.
        if attrs_have_cfg_test(&module.attrs) {
            let prev = self.in_test_module;
            self.in_test_module = true;
            syn::visit::visit_item_mod(self, module);
            self.in_test_module = prev;
        } else {
            syn::visit::visit_item_mod(self, module);
        }
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Only check migrate entry points
        if fn_name != "migrate" && !fn_name.starts_with("migrate_") {
            return;
        }

        // Skip anything inside a #[cfg(test)] module or gated on test itself.
        if self.in_test_module || attrs_have_cfg_test(&func.attrs) {
            return;
        }

        // Skip test functions (#[test], #[tokio::test], #[ink::test], ...)
        if is_test_attr(func) {
            return;
        }

        // Require the function to actually look like a migrate entry point
        // (takes DepsMut/Storage or carries an entry_point attr). This filters
        // pure `migrate_*` data converters that can never be invoked as a
        // migration.
        if !looks_like_migrate_entry(func) {
            return;
        }

        let body_src = fn_body_source(func);

        // Skip empty/stub implementations (just return Ok)
        let body_trimmed: String = body_src.chars().filter(|c| !c.is_whitespace()).collect();
        if body_trimmed.len() < 60 {
            return;
        }

        let has_auth = AUTH_PATTERNS.iter().any(|p| body_src.contains(p));
        let has_version = VERSION_PATTERNS.iter().any(|p| body_src.contains(p));

        // Guarded directly in its own body.
        if has_auth || has_version {
            return;
        }

        // Guarded by delegation: thin dispatcher whose every local callee is guarded.
        if self.guarded_by_callees(func) {
            return;
        }

        // Private/internal `migrate_*` helper whose guard lives in its caller
        // (the real entry point). Only the bare `migrate` is a true entry point;
        // `migrate_*` helpers inherit their caller's guard when one exists.
        if fn_name != "migrate" && self.any_caller_guarded(&fn_name) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "CW-010".to_string(),
            name: "unguarded-migrate-entry".to_string(),
            severity: Severity::Medium,
            confidence: Confidence::Medium,
            message: format!(
                "Migrate handler '{}' has no admin/sender check or version validation",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add admin authorization check (info.sender) and/or version validation (cw2::set_contract_version) in migrate handler".to_string(),
            chain: Chain::CosmWasm,
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
            Chain::CosmWasm,
            std::collections::HashMap::new(),
        );
        UnguardedMigrateDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unguarded_migrate() {
        let source = r#"
            fn migrate(deps: DepsMut, env: Env, msg: MigrateMsg) -> StdResult<Response> {
                CONFIG.save(deps.storage, &Config { new_field: msg.new_field })?;
                STATE.update(deps.storage, |mut s| -> StdResult<_> {
                    s.migrated = true;
                    Ok(s)
                })?;
                Ok(Response::new().add_attribute("action", "migrate"))
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect unguarded migrate");
        assert_eq!(findings[0].detector_id, "CW-010");
    }

    #[test]
    fn test_no_finding_with_admin_check() {
        let source = r#"
            fn migrate(deps: DepsMut, env: Env, info: MessageInfo, msg: MigrateMsg) -> StdResult<Response> {
                let admin = ADMIN.load(deps.storage)?;
                if info.sender != admin {
                    return Err(StdError::generic_err("unauthorized"));
                }
                CONFIG.save(deps.storage, &Config { new_field: msg.new_field })?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with admin/sender check"
        );
    }

    #[test]
    fn test_no_finding_with_version_check() {
        let source = r#"
            fn migrate(deps: DepsMut, env: Env, msg: MigrateMsg) -> StdResult<Response> {
                let ver = cw2 :: get_contract_version(deps.storage)?;
                set_contract_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                CONFIG.save(deps.storage, &Config { new_field: msg.new_field })?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with version validation"
        );
    }

    // FP idx 0: private `migrate_*` helper guarded by its caller (the entry point).
    #[test]
    fn test_no_finding_helper_guarded_by_caller() {
        let source = r#"
            pub fn migrate(deps: DepsMut, _env: Env, _msg: MigrateMsg) -> StdResult<Response> {
                cw2::set_contract_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                migrate_positions(deps.storage)?;
                Ok(Response::new())
            }

            fn migrate_positions(storage: &mut dyn Storage) -> StdResult<()> {
                let keys: Vec<Vec<u8>> = POSITIONS_V1
                    .keys(storage, None, None, Order::Ascending)
                    .collect::<StdResult<_>>()?;
                for k in keys {
                    let old = POSITIONS_V1.load(storage, &k)?;
                    POSITIONS.save(storage, &k, &PositionV2::from(old))?;
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Private migrate helper guarded by its caller should not flag"
        );
    }

    // FP idx 1: dispatch-style migrate entry whose guard lives in its callees.
    #[test]
    fn test_no_finding_dispatcher_with_guarded_callees() {
        let source = r#"
            #[cfg_attr(not(feature = "library"), entry_point)]
            pub fn migrate(deps: DepsMut, _env: Env, msg: MigrateMsg) -> Result<Response, ContractError> {
                match msg {
                    MigrateMsg::FromV1 {} => upgrade_from_v1(deps),
                    MigrateMsg::FromV2 {} => upgrade_from_v2(deps),
                }
            }

            fn upgrade_from_v1(deps: DepsMut) -> Result<Response, ContractError> {
                cw2::ensure_from_older_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                Ok(Response::new())
            }

            fn upgrade_from_v2(deps: DepsMut) -> Result<Response, ContractError> {
                cw2::ensure_from_older_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Dispatcher whose every arm is guarded should not flag"
        );
    }

    // FP idx 1 negative control: an unguarded arm must keep the finding.
    #[test]
    fn test_dispatcher_with_unguarded_callee_still_flags() {
        let source = r#"
            pub fn migrate(deps: DepsMut, _env: Env, msg: MigrateMsg) -> Result<Response, ContractError> {
                match msg {
                    MigrateMsg::FromV1 {} => upgrade_from_v1(deps),
                    MigrateMsg::FromV2 {} => upgrade_from_v2(deps),
                }
            }

            fn upgrade_from_v1(deps: DepsMut) -> Result<Response, ContractError> {
                cw2::ensure_from_older_version(deps.storage, CONTRACT_NAME, CONTRACT_VERSION)?;
                Ok(Response::new())
            }

            fn upgrade_from_v2(deps: DepsMut) -> Result<Response, ContractError> {
                CONFIG.save(deps.storage, &Config { migrated: true })?;
                STORE.update(deps.storage, |s| Ok(s))?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Dispatcher with an unguarded arm must still flag"
        );
    }

    // FP idx 2: pure data converter named migrate_* that cannot be an entry point.
    #[test]
    fn test_no_finding_pure_converter() {
        let source = r#"
            fn migrate_config(old: ConfigV1) -> ConfigV2 {
                ConfigV2 {
                    denom: old.denom,
                    fee_bps: old.fee_bps,
                    paused: false,
                    oracle: old.oracle,
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Pure struct converter should not flag"
        );
    }

    // FP idx 3: migrate test double inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_migrate_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;
                use cw_multi_test::ContractWrapper;

                fn migrate_stub(deps: DepsMut, _env: Env, msg: TestMigrateMsg) -> StdResult<Response> {
                    COUNTER.update(deps.storage, |c: u64| -> StdResult<_> { Ok(c + msg.bump) })?;
                    Ok(Response::new().add_attribute("action", "noop"))
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Migrate test double inside cfg(test) module should not flag"
        );
    }
}
