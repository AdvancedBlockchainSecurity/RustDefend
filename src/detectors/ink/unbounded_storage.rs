use quote::ToTokens;
use std::collections::HashMap;
use syn::visit::Visit;
use syn::{Expr, ImplItem, ImplItemFn, ItemImpl, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnboundedStorageDetector;

impl Detector for UnboundedStorageDetector {
    fn id(&self) -> &'static str {
        "INK-005"
    }
    fn name(&self) -> &'static str {
        "ink-unbounded-storage"
    }
    fn description(&self) -> &'static str {
        "Detects unbounded Vec push or Mapping insert without length check"
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
        let mut visitor = StorageVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct StorageVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// True if the attribute list marks a `#[cfg(test)]` item.
fn is_cfg_test(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let t = attr.meta.to_token_stream().to_string();
        t.contains("cfg") && t.contains("test")
    })
}

/// True if the fn is a test function (#[test], #[ink::test], #[tokio::test], ...).
fn is_test_fn(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        let path = attr
            .path()
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect::<Vec<_>>()
            .join("::");
        path == "test" || path.ends_with("::test")
    })
}

/// True if this method carries an `#[ink(message)]` attribute (constructors excluded).
fn is_ink_message(method: &ImplItemFn) -> bool {
    method.attrs.iter().any(|attr| {
        let tokens = attr.meta.to_token_stream().to_string();
        tokens.contains("ink") && tokens.contains("message")
    })
}

/// True if the method receiver is `&mut self` (or `mut self`).
fn takes_mut_self(method: &ImplItemFn) -> bool {
    match method.sig.receiver() {
        Some(r) => r.mutability.is_some(),
        None => false,
    }
}

/// Walk an expression down its receiver/field/index chain and report whether the
/// root base is the `self` value. Used to distinguish a *storage* push/insert
/// (`self.field.push(..)`) from a push into a stack-local Vec (`out.push(..)`).
fn expr_base_is_self(expr: &Expr) -> bool {
    let mut cur = expr;
    loop {
        match cur {
            Expr::MethodCall(m) => cur = m.receiver.as_ref(),
            Expr::Field(f) => cur = f.base.as_ref(),
            Expr::Index(i) => cur = i.expr.as_ref(),
            Expr::Paren(p) => cur = p.expr.as_ref(),
            Expr::Reference(r) => cur = r.expr.as_ref(),
            Expr::Try(t) => cur = t.expr.as_ref(),
            Expr::Await(a) => cur = a.base.as_ref(),
            Expr::Group(g) => cur = g.expr.as_ref(),
            Expr::Path(p) => {
                return p.path.segments.len() == 1 && p.path.segments[0].ident == "self";
            }
            _ => return false,
        }
    }
}

/// Conventional bound / capacity vocabulary that indicates a length guard is present.
/// These are *suppression* tokens only: matching one silences an otherwise-flagged
/// method, so extending the list can never create a new finding.
fn body_has_bound_vocab(body: &str) -> bool {
    // Note: a syn token stream prints `.len()` as `len ()`, so match that form.
    const TERMS: &[&str] = &[
        "len ()", "MAX_", "max_", "LIMIT", "limit", "CAP", "capacity", "BOUND",
    ];
    TERMS.iter().any(|t| body.contains(t))
}

impl<'a> StorageVisitor<'a> {
    /// Resolve sibling method calls made from `body` (calls of the form
    /// `self.<helper>(..)`) against the same-impl method bodies, and report whether
    /// any resolved helper body itself performs a length/bound check. This handles
    /// the common refactoring where the guard is factored into an `ensure_capacity()`
    /// style helper called before the push. Only sibling helpers whose bodies we can
    /// actually resolve are consulted (one level deep), so no name-based blanket skip.
    fn helper_enforces_bound(
        &self,
        body_calls: &[syn::ExprMethodCall],
        siblings: &HashMap<String, String>,
    ) -> bool {
        for call in body_calls {
            if !expr_base_is_self(call.receiver.as_ref()) {
                continue;
            }
            let name = call.method.to_string();
            if let Some(helper_body) = siblings.get(&name) {
                if body_has_bound_vocab(helper_body) {
                    return true;
                }
            }
        }
        false
    }

    fn check_method(&mut self, method: &ImplItemFn, siblings: &HashMap<String, String>) {
        if is_test_fn(&method.attrs) {
            return;
        }
        // Only #[ink(message)] methods are attacker-repeatable entry points.
        // Constructors run once at deploy time (deployer pays the deposit) so a
        // fixed number of pushes/inserts there cannot cause unbounded growth.
        if !is_ink_message(method) {
            return;
        }

        let body_src = method.block.to_token_stream().to_string();

        // Collect all method calls in the body once (AST, spacing-independent).
        let mut collector = MethodCallCollector { calls: vec![] };
        collector.visit_block(&method.block);

        // ---- Vec push without bounds check ----
        let storage_push = collector
            .calls
            .iter()
            .any(|c| c.method == "push" && expr_base_is_self(c.receiver.as_ref()));

        if storage_push && takes_mut_self(method) {
            let bounded = body_has_bound_vocab(&body_src)
                || self.helper_enforces_bound(&collector.calls, siblings);
            if !bounded {
                let line = span_to_line(&method.sig.ident.span());
                self.findings.push(Finding {
                    detector_id: "INK-005".to_string(),
                    name: "ink-unbounded-storage".to_string(),
                    severity: Severity::Medium,
                    confidence: Confidence::Medium,
                    message: format!(
                        "Method '{}' pushes to Vec without bounds check",
                        method.sig.ident
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&method.sig.ident.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Add a length check before pushing to prevent unbounded storage growth (DoS risk)".to_string(),
                    chain: Chain::Ink,
                });
            }
        }

        // ---- Mapping insert without bounds check ----
        let storage_inserts: Vec<&syn::ExprMethodCall> = collector
            .calls
            .iter()
            .filter(|c| c.method == "insert" && expr_base_is_self(c.receiver.as_ref()))
            .collect();

        if !storage_inserts.is_empty() {
            let has_bounds = body_src.contains("contains")
                || body_has_bound_vocab(&body_src)
                || self.helper_enforces_bound(&collector.calls, siblings);

            // Skip well-known ERC-20/ERC-721 standard methods where Mapping
            // insertions are bounded by design (one entry per caller/owner).
            let method_name = method.sig.ident.to_string();
            let is_standard_pattern = method_name == "approve"
                || method_name == "transfer"
                || method_name == "transfer_from"
                || method_name == "set_approval_for_all"
                || method_name.contains("_approve")
                || method_name.contains("set_");

            // Structural bounded-by-design case: the insert is keyed by the caller,
            // so at most one entry exists per account (same rationale as the standard
            // name skip-list above), regardless of the method's name.
            let derives_caller = body_src.contains("caller ()");
            let caller_keyed = derives_caller
                && storage_inserts.iter().any(|c| {
                    c.args
                        .first()
                        .map(|arg| arg.to_token_stream().to_string().contains("caller"))
                        .unwrap_or(false)
                });

            if !has_bounds && !is_standard_pattern && !caller_keyed {
                let line = span_to_line(&method.sig.ident.span());
                self.findings.push(Finding {
                    detector_id: "INK-005".to_string(),
                    name: "ink-unbounded-storage".to_string(),
                    severity: Severity::Medium,
                    confidence: Confidence::Medium,
                    message: format!(
                        "Method '{}' inserts into Mapping without bounds check",
                        method.sig.ident
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&method.sig.ident.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: "Consider adding bounds checks or requiring storage deposits for unbounded Mapping growth".to_string(),
                    chain: Chain::Ink,
                });
            }
        }
    }
}

impl<'ast, 'a> Visit<'ast> for StorageVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Skip #[cfg(test)] modules entirely — their contents are test fixtures.
        if is_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_impl(&mut self, item_impl: &'ast ItemImpl) {
        if is_cfg_test(&item_impl.attrs) {
            return;
        }

        // Build a map of every sibling method body in this impl so that guards
        // factored into helper functions can be resolved (one level deep).
        let mut siblings: HashMap<String, String> = HashMap::new();
        for it in &item_impl.items {
            if let ImplItem::Fn(f) = it {
                siblings.insert(
                    f.sig.ident.to_string(),
                    f.block.to_token_stream().to_string(),
                );
            }
        }

        for it in &item_impl.items {
            if let ImplItem::Fn(method) = it {
                self.check_method(method, &siblings);
            }
        }

        // Continue traversal for nested impls (e.g. inside fn bodies). Method
        // storage checks are performed explicitly above, not via this recursion.
        syn::visit::visit_item_impl(self, item_impl);
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
            Chain::Ink,
            std::collections::HashMap::new(),
        );
        UnboundedStorageDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unbounded_push() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn add_item(&mut self, item: u32) {
                    self.items.push(item);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect unbounded push");
    }

    #[test]
    fn test_no_finding_with_len_check() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn add_item(&mut self, item: u32) {
                    assert!(self.items.len() < MAX_ITEMS);
                    self.items.push(item);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with length check");
    }

    // ---- FP regression tests (should NOT flag) ----

    // FP idx 0: read-only view method building a local Vec return value.
    #[test]
    fn test_no_finding_local_vec_in_view_method() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn get_admins(&self) -> Vec<AccountId> {
                    let mut out = Vec::new();
                    out.push(self.owner);
                    out.push(self.treasurer);
                    out
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a local Vec push in a &self view method"
        );
    }

    // FP idx 1: one-time initialization push inside a constructor.
    #[test]
    fn test_no_finding_constructor_push() {
        let source = r#"
            impl MyContract {
                #[ink(constructor)]
                pub fn new(admin: AccountId) -> Self {
                    let mut contract = Self::default();
                    contract.admins.push(admin);
                    contract
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a fixed push inside a constructor"
        );
    }

    // FP idx 2: per-caller Mapping insert keyed by env().caller().
    #[test]
    fn test_no_finding_caller_keyed_insert() {
        let source = r#"
            impl MyContract {
                #[ink(message, payable)]
                pub fn deposit(&mut self) {
                    let caller = self.env().caller();
                    let value = self.env().transferred_value();
                    self.deposits.insert(caller, &value);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a caller-keyed Mapping insert"
        );
    }

    // FP idx 3: bounds check via a LIMIT constant and counter field.
    #[test]
    fn test_no_finding_limit_constant_guard() {
        let source = r#"
            const ITEM_LIMIT: u32 = 100;

            impl MyContract {
                #[ink(message)]
                pub fn add_item(&mut self, item: u32) {
                    assert!(self.item_count < ITEM_LIMIT);
                    self.item_count += 1;
                    self.items.push(item);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a push guarded by a LIMIT constant"
        );
    }

    // FP idx 4: length guard factored into a helper function.
    #[test]
    fn test_no_finding_helper_bound_check() {
        let source = r#"
            impl MyContract {
                fn ensure_capacity(&self) {
                    assert!(self.items.len() < MAX_ITEMS);
                }

                #[ink(message)]
                pub fn add_item(&mut self, item: u32) {
                    self.ensure_capacity();
                    self.items.push(item);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the bound check is in a called helper"
        );
    }

    // Sanity: an arbitrary-key insert under a non-standard name still fires.
    #[test]
    fn test_still_detects_arbitrary_key_insert() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn register(&mut self, id: u32, data: Data) {
                    self.entries.insert(id, &data);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag an unbounded arbitrary-key Mapping insert"
        );
    }
}
