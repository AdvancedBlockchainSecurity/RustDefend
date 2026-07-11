use quote::ToTokens;
use std::collections::HashMap;
use syn::visit::Visit;
use syn::{Attribute, Expr, ExprCall, ExprLit, ImplItemFn, ItemFn, ItemMod, Lit};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct StorageCollisionDetector;

impl Detector for StorageCollisionDetector {
    fn id(&self) -> &'static str {
        "CW-004"
    }
    fn name(&self) -> &'static str {
        "storage-collision"
    }
    fn description(&self) -> &'static str {
        "Detects duplicate storage prefixes in Map::new() / Item::new()"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();

        // Collect all storage constructor calls with string prefixes
        let mut prefix_locations: HashMap<String, Vec<usize>> = HashMap::new();
        let mut visitor = StorageVisitor {
            prefixes: &mut prefix_locations,
            in_fn_body: false,
        };
        visitor.visit_file(&ctx.ast);

        // Report duplicates
        for (prefix, lines) in &prefix_locations {
            if lines.len() > 1 {
                for &line in &lines[1..] {
                    findings.push(Finding {
                        detector_id: "CW-004".to_string(),
                        name: "storage-collision".to_string(),
                        severity: Severity::High,
                        confidence: Confidence::High,
                        message: format!(
                            "Duplicate storage prefix '{}' (also used at line {})",
                            prefix, lines[0]
                        ),
                        file: ctx.file_path.clone(),
                        line,
                        column: 1,
                        snippet: snippet_at_line(&ctx.source, line),
                        recommendation:
                            "Each storage item must have a unique prefix to prevent data collisions"
                                .to_string(),
                        chain: Chain::CosmWasm,
                    });
                }
            }
        }

        findings
    }
}

/// True if the attribute list carries `#[cfg(test)]`.
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path().is_ident("cfg") && attr.meta.to_token_stream().to_string().contains("test")
    })
}

/// True if the attribute list marks a test function
/// (`#[test]`, `#[tokio::test]`, `#[ink::test]`, ...).
fn is_test_fn(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let path_str = attr
            .path()
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect::<Vec<_>>()
            .join("::");
        path_str == "test" || path_str.ends_with("::test")
    })
}

struct StorageVisitor<'a> {
    prefixes: &'a mut HashMap<String, Vec<usize>>,
    /// Whether the visitor is currently walking inside a function/method body.
    /// Only module-level const/static storage declarations represent distinct
    /// global storage items; function-local re-declarations (e.g. the standard
    /// cw-storage-plus migration idiom) are deliberate aliases of the same
    /// namespace and must NOT be treated as collisions.
    in_fn_body: bool,
}

impl<'ast, 'a> Visit<'ast> for StorageVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Skip `#[cfg(test)]` modules entirely: test-only code is compiled out
        // of the deployed wasm, so it can never cause an on-chain collision.
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        // Skip test functions outright, and record declarations inside any
        // function body as non-global (aliases, not distinct storage items).
        if is_test_fn(&node.attrs) {
            return;
        }
        let prev = self.in_fn_body;
        self.in_fn_body = true;
        syn::visit::visit_item_fn(self, node);
        self.in_fn_body = prev;
    }

    fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
        if is_test_fn(&node.attrs) {
            return;
        }
        let prev = self.in_fn_body;
        self.in_fn_body = true;
        syn::visit::visit_impl_item_fn(self, node);
        self.in_fn_body = prev;
    }

    fn visit_expr_call(&mut self, call: &'ast ExprCall) {
        let func_str = call.func.to_token_stream().to_string();

        // Match Map::new, Item::new, Deque::new etc.
        if (func_str.contains(":: new") || func_str.contains("::new"))
            && (func_str.contains("Map")
                || func_str.contains("Item")
                || func_str.contains("Deque")
                || func_str.contains("SnapshotMap")
                || func_str.contains("SnapshotItem"))
        {
            // Extract the first string argument (prefix)
            if let Some(first_arg) = call.args.first() {
                if let Expr::Lit(ExprLit {
                    lit: Lit::Str(s), ..
                }) = first_arg
                {
                    // Only module-level (const/static) declarations describe
                    // distinct global storage items. Function-local ones are
                    // deliberate aliases (migration idiom, test probes).
                    if !self.in_fn_body {
                        let prefix = s.value();
                        let line = span_to_line(&s.span());
                        self.prefixes.entry(prefix).or_default().push(line);
                    }
                }
            }
        }

        syn::visit::visit_expr_call(self, call);
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
        StorageCollisionDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_duplicate_prefix() {
        let source = r#"
            const BALANCES: Map<&Addr, Uint128> = Map::new("balances");
            const ALLOWANCES: Map<&Addr, Uint128> = Map::new("balances");
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect duplicate prefix");
    }

    #[test]
    fn test_no_finding_unique_prefixes() {
        let source = r#"
            const BALANCES: Map<&Addr, Uint128> = Map::new("balances");
            const ALLOWANCES: Map<(&Addr, &Addr), Uint128> = Map::new("allowances");
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag unique prefixes");
    }

    // FP idx 0: the cw-storage-plus migration idiom deliberately re-opens the
    // SAME namespace with a legacy value type inside a function body. Both
    // constructors refer to the same logical item by design, so this must not
    // be flagged.
    #[test]
    fn test_no_finding_migration_reopens_namespace() {
        let source = r#"
            pub const BALANCES: Map<&Addr, Uint128> = Map::new("balances");

            pub fn migrate(deps: DepsMut, _env: Env, _msg: MigrateMsg) -> StdResult<Response> {
                let legacy: Map<&Addr, OldBalance> = Map::new("balances");
                let keys: Vec<_> = legacy
                    .keys(deps.storage, None, None, Order::Ascending)
                    .collect::<StdResult<_>>()?;
                for k in keys {
                    let old = legacy.load(deps.storage, &k)?;
                    BALANCES.save(deps.storage, &k, &Uint128::from(old.amount))?;
                }
                Ok(Response::default())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Migration re-opening the same namespace must not be flagged"
        );
    }

    // FP idx 1: a #[cfg(test)] module re-declares a production prefix to inspect
    // storage in unit tests. Test-only code is compiled out of the deployed
    // contract, so no on-chain collision is possible.
    #[test]
    fn test_no_finding_cfg_test_module_reopens_key() {
        let source = r#"
            pub const CONFIG: Item<Config> = Item::new("config");

            #[cfg(test)]
            mod tests {
                use super::*;

                #[test]
                fn instantiate_writes_config() {
                    let probe: Item<Config> = Item::new("config");
                    assert_eq!(probe.load(&deps.storage).unwrap().owner, "admin");
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Duplicate prefix inside #[cfg(test)] must not be flagged"
        );
    }
}
