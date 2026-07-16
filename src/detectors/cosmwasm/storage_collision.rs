use quote::ToTokens;
use std::collections::{HashMap, HashSet};
use syn::visit::Visit;
use syn::{
    Attribute, Expr, ExprCall, ExprLit, ExprPath, ImplItemFn, ItemConst, ItemFn, ItemMod,
    ItemStatic, Lit, LitStr,
};

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

        // First pass: index the module-level `const`/`static` items that own each
        // prefix. A function-local constructor can only be an alias of a global
        // storage item if such an item actually exists to be aliased.
        let mut owner_visitor = ModuleOwnerVisitor {
            owners: HashMap::new(),
        };
        owner_visitor.visit_file(&ctx.ast);

        // Second pass: collect all storage constructor calls with string prefixes
        let mut prefix_locations: HashMap<String, Vec<usize>> = HashMap::new();
        let mut visitor = StorageVisitor {
            prefixes: &mut prefix_locations,
            module_owners: &owner_visitor.owners,
            fn_refs: HashSet::new(),
            fn_seen: HashSet::new(),
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

/// If `call` is a cw-storage-plus constructor (`Map::new`, `Item::new`, ...)
/// whose first argument is a string literal, return that literal prefix.
fn storage_prefix_lit(call: &ExprCall) -> Option<&LitStr> {
    let func_str = call.func.to_token_stream().to_string();

    // Match Map::new, Item::new, Deque::new etc.
    if !((func_str.contains(":: new") || func_str.contains("::new"))
        && (func_str.contains("Map")
            || func_str.contains("Item")
            || func_str.contains("Deque")
            || func_str.contains("SnapshotMap")
            || func_str.contains("SnapshotItem")))
    {
        return None;
    }

    // Extract the first string argument (prefix)
    match call.args.first() {
        Some(Expr::Lit(ExprLit {
            lit: Lit::Str(s), ..
        })) => Some(s),
        _ => None,
    }
}

/// Same as `storage_prefix_lit`, for an expression that is itself the
/// constructor call (a `const`/`static` initializer).
fn storage_prefix_of_expr(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Call(call) => storage_prefix_lit(call).map(|s| s.value()),
        _ => None,
    }
}

/// First pass: maps each prefix to the module-level `const`/`static` items that
/// declare it. Only these items are global storage declarations that a
/// function-local constructor could legitimately be re-opening.
struct ModuleOwnerVisitor {
    owners: HashMap<String, Vec<String>>,
}

impl<'ast> Visit<'ast> for ModuleOwnerVisitor {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Test-only code is compiled out of the deployed wasm; it owns nothing.
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    // Function bodies cannot declare a global storage item, so nothing inside
    // one can own a prefix.
    fn visit_item_fn(&mut self, _node: &'ast ItemFn) {}
    fn visit_impl_item_fn(&mut self, _node: &'ast ImplItemFn) {}

    fn visit_item_const(&mut self, node: &'ast ItemConst) {
        if let Some(prefix) = storage_prefix_of_expr(&node.expr) {
            self.owners
                .entry(prefix)
                .or_default()
                .push(node.ident.to_string());
        }
    }

    fn visit_item_static(&mut self, node: &'ast ItemStatic) {
        if let Some(prefix) = storage_prefix_of_expr(&node.expr) {
            self.owners
                .entry(prefix)
                .or_default()
                .push(node.ident.to_string());
        }
    }
}

/// Collects every identifier used as a value path in a subtree, so we can ask
/// whether a function body actually works with a given module-level item.
#[derive(Default)]
struct PathIdentCollector {
    idents: HashSet<String>,
}

impl<'ast> Visit<'ast> for PathIdentCollector {
    fn visit_expr_path(&mut self, node: &'ast ExprPath) {
        if let Some(seg) = node.path.segments.last() {
            self.idents.insert(seg.ident.to_string());
        }
        syn::visit::visit_expr_path(self, node);
    }
}

/// Identifiers referenced anywhere in `block`.
fn referenced_idents(block: &syn::Block) -> HashSet<String> {
    let mut c = PathIdentCollector::default();
    c.visit_block(block);
    c.idents
}

struct StorageVisitor<'a> {
    prefixes: &'a mut HashMap<String, Vec<usize>>,
    /// Prefix -> module-level `const`/`static` items declaring it.
    module_owners: &'a HashMap<String, Vec<String>>,
    /// Identifiers referenced by the function body currently being walked.
    fn_refs: HashSet<String>,
    /// Prefixes already recorded for the body currently being walked: re-opening
    /// one namespace several times in a single body is one declaration site.
    fn_seen: HashSet<String>,
    /// Whether the visitor is currently walking inside a function/method body.
    in_fn_body: bool,
}

impl<'a> StorageVisitor<'a> {
    /// Walk a function body with its own reference/alias bookkeeping.
    fn in_fn<F: FnOnce(&mut Self)>(&mut self, block: &syn::Block, walk: F) {
        let prev_in = self.in_fn_body;
        let prev_refs = std::mem::replace(&mut self.fn_refs, referenced_idents(block));
        let prev_seen = std::mem::take(&mut self.fn_seen);
        self.in_fn_body = true;
        walk(self);
        self.in_fn_body = prev_in;
        self.fn_refs = prev_refs;
        self.fn_seen = prev_seen;
    }

    /// Whether this constructor site declares a storage item in its own right.
    ///
    /// A module-level declaration always does. A function-local one is a mere
    /// alias only when the body *also works with* the module-level item that
    /// owns the prefix -- that is what the cw-storage-plus migration idiom does:
    /// it reads through the local legacy handle and writes through the global
    /// one, so both names denote the same logical item. A body that opens a
    /// namespace and never touches its owner is treating that namespace as an
    /// item of its own, which is precisely how two logical items collide.
    fn declares_item(&mut self, prefix: &str) -> bool {
        if !self.in_fn_body {
            return true;
        }
        let aliases_owner = self
            .module_owners
            .get(prefix)
            .is_some_and(|owners| owners.iter().any(|o| self.fn_refs.contains(o)));
        if aliases_owner {
            return false;
        }
        // `insert` is false when this body already opened the same namespace.
        self.fn_seen.insert(prefix.to_string())
    }
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
        // Skip test functions outright: they are compiled out of the wasm.
        if is_test_fn(&node.attrs) {
            return;
        }
        self.in_fn(&node.block, |v| syn::visit::visit_item_fn(v, node));
    }

    fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
        if is_test_fn(&node.attrs) {
            return;
        }
        self.in_fn(&node.block, |v| syn::visit::visit_impl_item_fn(v, node));
    }

    fn visit_expr_call(&mut self, call: &'ast ExprCall) {
        if let Some(lit) = storage_prefix_lit(call) {
            let prefix = lit.value();
            if self.declares_item(&prefix) {
                let line = span_to_line(&lit.span());
                self.prefixes.entry(prefix).or_default().push(line);
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

    // MUST STILL FLAG: two DISTINCT logical items (staked principal, reward
    // points) accidentally share the "stakes" namespace, so a reward credit
    // overwrites the caller's principal. The handlers open their maps lazily in
    // the body instead of using module-level consts -- a placement difference
    // only. ADV-206's `!in_fn_body` guard silenced this real High/High bug.
    #[test]
    fn test_still_flags_handler_local_colliding_maps() {
        let source = r#"
            pub fn execute_stake(deps: DepsMut, info: MessageInfo, amount: Uint128) -> StdResult<Response> {
                let stakes: Map<&Addr, Uint128> = Map::new("stakes");
                let current = stakes.may_load(deps.storage, &info.sender)?.unwrap_or_default();
                stakes.save(deps.storage, &info.sender, &(current + amount))?;
                Ok(Response::new())
            }

            pub fn execute_accrue_rewards(deps: DepsMut, user: String, amount: Uint128) -> StdResult<Response> {
                let rewards: Map<&Addr, Uint128> = Map::new("stakes");
                let addr = deps.api.addr_validate(&user)?;
                let current = rewards.may_load(deps.storage, &addr)?.unwrap_or_default();
                rewards.save(deps.storage, &addr, &(current + amount))?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.detector_id == "CW-004"),
            "Colliding prefix declared inside handler bodies must still be flagged"
        );
    }

    // MUST STILL FLAG: the collision hides behind a module-level owner. The body
    // opens "balances" for an unrelated item and never touches BALANCES, so this
    // is a real collision and not the migration idiom.
    #[test]
    fn test_still_flags_local_shadowing_owner_it_never_uses() {
        let source = r#"
            pub const BALANCES: Map<&Addr, Uint128> = Map::new("balances");

            pub fn record_vote(deps: DepsMut, info: MessageInfo, weight: Uint128) -> StdResult<Response> {
                let votes: Map<&Addr, Uint128> = Map::new("balances");
                votes.save(deps.storage, &info.sender, &weight)?;
                Ok(Response::default())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.detector_id == "CW-004"),
            "A body that re-opens a namespace without using its owner is a collision"
        );
    }

    // A handler re-opening the same namespace repeatedly is one declaration
    // site, not a self-collision.
    #[test]
    fn test_no_finding_same_body_reopens_one_namespace() {
        let source = r#"
            pub fn tally(deps: DepsMut, a: &Addr, b: &Addr) -> StdResult<Uint128> {
                let left: Map<&Addr, Uint128> = Map::new("stakes");
                let right: Map<&Addr, Uint128> = Map::new("stakes");
                Ok(left.load(deps.storage, a)? + right.load(deps.storage, b)?)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Re-opening one namespace within a single body is not a collision"
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
