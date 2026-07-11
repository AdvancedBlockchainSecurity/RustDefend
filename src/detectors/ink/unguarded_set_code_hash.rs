use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, ImplItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnguardedSetCodeHashDetector;

impl Detector for UnguardedSetCodeHashDetector {
    fn id(&self) -> &'static str {
        "INK-011"
    }
    fn name(&self) -> &'static str {
        "unguarded-set-code-hash"
    }
    fn description(&self) -> &'static str {
        "Detects set_code_hash usage without admin/owner verification"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Ink
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();

        // Collect every impl method in the file (skipping #[cfg(test)] modules and
        // #[test]/#[ink::test]/etc. functions) so we can reason about delegated auth
        // (callee guards) and caller-guarded private helpers.
        let mut collector = MethodCollector {
            records: Vec::new(),
        };
        collector.visit_file(&ctx.ast);
        let records = collector.records;

        // Map method name -> indices, for resolving delegated calls in-file.
        let mut name_map: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, r) in records.iter().enumerate() {
            name_map.entry(r.name.clone()).or_default().push(i);
        }

        for (i, r) in records.iter().enumerate() {
            if !r.has_set_code_hash_call {
                continue;
            }

            let mut visited = Vec::new();
            if fully_guarded(&records, &name_map, i, &mut visited, 0) {
                continue;
            }

            findings.push(Finding {
                detector_id: "INK-011".to_string(),
                name: "unguarded-set-code-hash".to_string(),
                severity: Severity::Medium,
                confidence: Confidence::Medium,
                message: format!(
                    "Method '{}' calls set_code_hash without admin/owner verification",
                    r.name
                ),
                file: ctx.file_path.clone(),
                line: r.line,
                column: r.column,
                snippet: snippet_at_line(&ctx.source, r.line),
                recommendation: "Add caller verification (e.g., assert_eq!(self.env().caller(), self.owner)) before set_code_hash to prevent unauthorized contract upgrades".to_string(),
                chain: Chain::Ink,
            });
        }

        findings
    }
}

/// Substring auth markers searched inside a method *body*.
const AUTH_PATTERNS: &[&str] = &[
    "caller",
    "admin",
    "owner",
    "ADMIN",
    "OWNER",
    "is_admin",
    "is_owner",
    "only_owner",
    "only_admin",
    "ensure_owner",
    "assert_eq !",
    "assert_eq!",
];

/// Auth stems searched inside modifier/access-control *attributes*.
const ATTR_AUTH_STEMS: &[&str] = &[
    "owner",
    "admin",
    "role",
    "auth",
    "governance",
    "only_",
    "OWNER",
    "ADMIN",
];

/// A single impl method extracted from the file.
struct MethodRecord {
    name: String,
    line: usize,
    column: usize,
    /// Names of methods/functions called from this body (method-call idents and
    /// last path segments of function calls). Derived from the parsed AST, so a
    /// `set_code_hash` appearing only inside a string literal never shows up here.
    calls: Vec<String>,
    has_set_code_hash_call: bool,
    /// Auth pattern present directly in this method's body tokens.
    has_direct_auth: bool,
    /// Auth provided by a modifier/access-control attribute on the method.
    has_attr_auth: bool,
    /// True if the method is an externally dispatchable ink! entry point.
    is_entry_point: bool,
}

struct MethodCollector {
    records: Vec<MethodRecord>,
}

impl<'ast> Visit<'ast> for MethodCollector {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Never descend into #[cfg(test)] modules: that code is host-only test
        // scaffolding and is never part of the deployed contract.
        if has_attribute_with_value(&m.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        let name = method.sig.ident.to_string();

        // Skip test functions (name-based, plus #[test]/#[ink::test]/#[tokio::test]/
        // #[ink_e2e::test] attribute-based).
        if is_test_method(&name, &method.attrs) {
            return;
        }

        let calls = collect_call_names(method);
        let has_set_code_hash_call = calls.iter().any(|c| c == "set_code_hash");

        let body_src = method.block.to_token_stream().to_string();
        let has_direct_auth = AUTH_PATTERNS.iter().any(|p| body_src.contains(p));
        let has_attr_auth = attr_provides_auth(&method.attrs);
        let is_entry_point = has_nested_attribute(&method.attrs, "ink", "message")
            || has_nested_attribute(&method.attrs, "ink", "constructor");

        self.records.push(MethodRecord {
            name,
            line: span_to_line(&method.sig.ident.span()),
            column: span_to_column(&method.sig.ident.span()),
            calls,
            has_set_code_hash_call,
            has_direct_auth,
            has_attr_auth,
            is_entry_point,
        });

        syn::visit::visit_impl_item_fn(self, method);
    }
}

/// Returns true if the method is a test function that never ships on-chain.
fn is_test_method(name: &str, attrs: &[Attribute]) -> bool {
    if name.starts_with("test_") || name.ends_with("_test") {
        return true;
    }
    attrs.iter().any(|a| {
        a.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

/// Collect the names of all calls (method-call idents and function-call path tails)
/// inside a method body from the parsed AST.
fn collect_call_names(method: &ImplItemFn) -> Vec<String> {
    struct CallNameCollector {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for CallNameCollector {
        fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
            self.names.push(node.method.to_string());
            syn::visit::visit_expr_method_call(self, node);
        }
        fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
            if let Expr::Path(p) = node.func.as_ref() {
                if let Some(seg) = p.path.segments.last() {
                    self.names.push(seg.ident.to_string());
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }
    let mut c = CallNameCollector { names: Vec::new() };
    c.visit_block(&method.block);
    c.names
}

/// Detect an owner/admin/role modifier or access-control attribute on a method,
/// e.g. `#[openbrush::modifiers(only_owner)]` or `#[access_control(only_role(..))]`.
/// Doc and cfg attributes are ignored so their text can't spuriously match.
fn attr_provides_auth(attrs: &[Attribute]) -> bool {
    for attr in attrs {
        let path = attr
            .path()
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect::<Vec<_>>()
            .join("::");

        if path == "doc" || path == "cfg" {
            continue;
        }

        // Bare guard attributes like #[only_owner] / #[ensure_owner].
        if matches!(
            path.as_str(),
            "only_owner" | "only_admin" | "only_role" | "ensure_owner"
        ) {
            return true;
        }

        // Modifier / access-control style attributes: require an auth stem in the
        // argument tokens so non-auth modifiers (e.g. when_not_paused) don't match.
        if path.contains("modifier") || path.contains("access_control") {
            let tokens = attr.to_token_stream().to_string();
            if ATTR_AUTH_STEMS.iter().any(|s| tokens.contains(s)) {
                return true;
            }
        }
    }
    false
}

/// True if the method at `idx` is guarded by a check it performs directly, or by a
/// modifier attribute, or by delegating to an in-file helper whose resolved body
/// actually contains an auth check.
fn resolves_guard(
    records: &[MethodRecord],
    name_map: &HashMap<String, Vec<usize>>,
    idx: usize,
    visited: &mut Vec<usize>,
    depth: usize,
) -> bool {
    if depth > 8 {
        return false;
    }
    let r = &records[idx];
    if r.has_direct_auth || r.has_attr_auth {
        return true;
    }
    if visited.contains(&idx) {
        return false;
    }
    visited.push(idx);

    for callee in &r.calls {
        if let Some(indices) = name_map.get(callee) {
            for &ci in indices {
                if ci == idx {
                    continue;
                }
                if resolves_guard(records, name_map, ci, visited, depth + 1) {
                    return true;
                }
            }
        }
    }
    false
}

/// True if every externally reachable path to this method passes an auth check.
/// A method is fully guarded when it guards itself/delegates (resolves_guard), or
/// when it is not an on-chain entry point and every in-file caller is itself fully
/// guarded. Methods with no in-file callers that don't guard themselves are NOT
/// suppressed (conservative: a genuinely unguarded upgrade path still fires).
fn fully_guarded(
    records: &[MethodRecord],
    name_map: &HashMap<String, Vec<usize>>,
    idx: usize,
    visited: &mut Vec<usize>,
    depth: usize,
) -> bool {
    if depth > 8 {
        return false;
    }

    let mut rv = Vec::new();
    if resolves_guard(records, name_map, idx, &mut rv, 0) {
        return true;
    }

    // Only non-entry-point (private) helpers can inherit their caller's guard.
    // An unguarded #[ink(message)]/#[ink(constructor)] is directly reachable and
    // must always fire.
    if records[idx].is_entry_point {
        return false;
    }

    if visited.contains(&idx) {
        return false;
    }
    visited.push(idx);

    let name = &records[idx].name;
    let callers: Vec<usize> = (0..records.len())
        .filter(|&c| c != idx && records[c].calls.iter().any(|x| x == name))
        .collect();

    if callers.is_empty() {
        return false;
    }

    callers.iter().all(|&c| {
        let mut v = visited.clone();
        fully_guarded(records, name_map, c, &mut v, depth + 1)
    })
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
            Chain::Ink,
            std::collections::HashMap::new(),
        );
        UnguardedSetCodeHashDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unguarded_set_code_hash() {
        let source = r#"
            impl MyContract {
                pub fn upgrade(&mut self, new_code_hash: Hash) {
                    self.env().set_code_hash(&new_code_hash).expect("upgrade failed");
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect unguarded set_code_hash"
        );
        assert_eq!(findings[0].detector_id, "INK-011");
    }

    #[test]
    fn test_no_finding_with_owner_check() {
        let source = r#"
            impl MyContract {
                pub fn upgrade(&mut self, new_code_hash: Hash) {
                    let caller = self.env().caller();
                    assert_eq!(caller, self.owner, "only owner can upgrade");
                    self.env().set_code_hash(&new_code_hash).expect("upgrade failed");
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with owner/caller check"
        );
    }

    #[test]
    fn test_no_finding_with_admin_guard() {
        let source = r#"
            impl MyContract {
                pub fn upgrade(&mut self, new_code_hash: Hash) {
                    self.ensure_owner();
                    self.env().set_code_hash(&new_code_hash).expect("upgrade failed");
                }
            }
        "#;
        // ensure_owner doesn't match our patterns, but "owner" substring does
        // Actually let me check - "ensure_owner" contains "owner"
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with admin guard method"
        );
    }

    // FP idx 0: OpenBrush modifier attribute provides the guard.
    #[test]
    fn test_no_finding_with_openbrush_modifier() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                #[openbrush::modifiers(only_owner)]
                pub fn upgrade(&mut self, new_code_hash: Hash) -> Result<(), OwnableError> {
                    self.env().set_code_hash(&new_code_hash).unwrap();
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when #[openbrush::modifiers(only_owner)] guards the method"
        );
    }

    // FP idx 1: private helper called only from a guarded entry point.
    #[test]
    fn test_no_finding_private_helper_guarded_caller() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn upgrade(&mut self, new_code_hash: Hash) {
                    assert_eq!(self.env().caller(), self.owner);
                    self.do_upgrade(new_code_hash);
                }

                fn do_upgrade(&mut self, new_code_hash: Hash) {
                    self.env().set_code_hash(&new_code_hash).unwrap();
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a private helper whose only caller performs the owner check"
        );
    }

    // FP idx 2: auth helper whose name lacks the owner/admin/caller substrings,
    // resolved in-file to confirm it really checks the caller.
    #[test]
    fn test_no_finding_delegated_named_auth_helper() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn upgrade(&mut self, new_code_hash: Hash) -> Result<(), Error> {
                    self.ensure_authorized()?;
                    self.env().set_code_hash(&new_code_hash).map_err(|_| Error::UpgradeFailed)
                }

                fn ensure_authorized(&self) -> Result<(), Error> {
                    if self.env().caller() != self.governance {
                        return Err(Error::NotAuthorized);
                    }
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a resolvable helper performs the caller check"
        );
    }

    // FP idx 2b: helper name avoids the substrings AND its body has no auth check
    // and cannot be resolved to one -> must STILL fire (no false negative).
    #[test]
    fn test_still_fires_when_helper_has_no_real_check() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn upgrade(&mut self, new_code_hash: Hash) -> Result<(), Error> {
                    self.prepare()?;
                    self.env().set_code_hash(&new_code_hash).map_err(|_| Error::UpgradeFailed)
                }

                fn prepare(&self) -> Result<(), Error> {
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag when the delegated helper performs no auth check"
        );
    }

    // FP idx 3: methods inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;
                struct Harness { contract: MyContract }
                impl Harness {
                    fn perform_upgrade(&mut self, h: Hash) {
                        self.contract.env().set_code_hash(&h).unwrap();
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag upgrade helpers inside #[cfg(test)] modules"
        );
    }

    // FP idx 4: "set_code_hash" appears only inside a string literal.
    #[test]
    fn test_no_finding_string_literal_only() {
        let source = r#"
            impl Error {
                pub fn message(&self) -> &'static str {
                    match self {
                        Error::UpgradeFailed => "set_code_hash rejected by runtime",
                        Error::Paused => "contract paused",
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when set_code_hash appears only in a string literal"
        );
    }
}
