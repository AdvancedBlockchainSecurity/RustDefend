use quote::ToTokens;
use std::collections::{HashMap, HashSet};
use syn::punctuated::Punctuated;
use syn::visit::Visit;
use syn::{Expr, ImplItem, ImplItemFn, ItemImpl, ItemMod, Token};

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

/// Strip wrappers that do not change what an expression *is* for bound analysis:
/// parens, groups, `&`/`&mut` borrows and `as` casts (`self.v.len() as u32 < MAX`).
fn strip_expr(mut e: &Expr) -> &Expr {
    loop {
        e = match e {
            Expr::Paren(p) => p.expr.as_ref(),
            Expr::Group(g) => g.expr.as_ref(),
            Expr::Reference(r) => r.expr.as_ref(),
            Expr::Cast(c) => c.expr.as_ref(),
            _ => return e,
        };
    }
}

/// True if `expr` reads contract state: an `Expr::Field` chain rooted at `self`
/// (`self.items`, `self.inner.items`, `self.rows[i]`). Method-call hops are
/// deliberately *not* traversed, so `self.env().block_timestamp()` is an
/// environment query rather than a storage read and does not qualify.
fn is_storage_field_read(expr: &Expr) -> bool {
    let mut cur = strip_expr(expr);
    let mut saw_field = false;
    loop {
        match cur {
            Expr::Field(f) => {
                saw_field = true;
                cur = strip_expr(f.base.as_ref());
            }
            Expr::Index(i) => cur = strip_expr(i.expr.as_ref()),
            Expr::Path(p) => {
                return saw_field
                    && p.path.segments.len() == 1
                    && p.path.segments[0].ident == "self";
            }
            _ => return false,
        }
    }
}

/// True if the expression subtree measures the length of a storage collection
/// (`self.items.len()`). Callers only consult this on *operands of a comparison*,
/// so a bare value computation such as `self.v.len().checked_sub(1)` in ordinary
/// statement position never counts as a bound check.
fn contains_storage_len_call(expr: &Expr) -> bool {
    struct LenFinder {
        found: bool,
    }
    impl<'ast> Visit<'ast> for LenFinder {
        fn visit_expr_method_call(&mut self, c: &'ast syn::ExprMethodCall) {
            if c.method == "len" && is_storage_field_read(c.receiver.as_ref()) {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, c);
        }
    }
    let mut f = LenFinder { found: false };
    f.visit_expr(expr);
    f.found
}

/// True if `expr` is a compile-time bound: an integer literal, a SCREAMING_SNAKE
/// constant path (`MAX_ITEMS`, `Self::LIMIT`), or arithmetic over those.
fn is_constant_bound(expr: &Expr) -> bool {
    match strip_expr(expr) {
        Expr::Lit(l) => matches!(l.lit, syn::Lit::Int(_)),
        Expr::Path(p) => p
            .path
            .segments
            .last()
            .map(|s| {
                let n = s.ident.to_string();
                n.chars().any(|c| c.is_ascii_uppercase())
                    && !n.chars().any(|c| c.is_ascii_lowercase())
            })
            .unwrap_or(false),
        Expr::Binary(b) => is_constant_bound(&b.left) && is_constant_bound(&b.right),
        _ => false,
    }
}

/// Comparison operators that can express a bound.
fn is_comparison_op(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::Lt(_)
            | syn::BinOp::Le(_)
            | syn::BinOp::Gt(_)
            | syn::BinOp::Ge(_)
            | syn::BinOp::Eq(_)
            | syn::BinOp::Ne(_)
    )
}

/// Compound assignments (`+=`, `-=`, ...) — how a manual length counter is bumped.
fn is_assign_op(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
    )
}

/// Assert/require families whose arguments are *conditions the code enforces*,
/// as opposed to values it merely computes.
fn is_assert_family(path: &syn::Path) -> bool {
    path.segments
        .last()
        .map(|s| {
            matches!(
                s.ident.to_string().as_str(),
                "assert"
                    | "assert_eq"
                    | "assert_ne"
                    | "debug_assert"
                    | "debug_assert_eq"
                    | "debug_assert_ne"
                    | "require"
                    | "ensure"
            )
        })
        .unwrap_or(false)
}

/// Structural facts about one method body, gathered in a single AST pass.
#[derive(Default)]
struct BodyFacts {
    /// Expressions the body actually enforces or branches on: assert!/require!
    /// arguments and `if`/`while` conditions. A bound check must appear here —
    /// merely *mentioning* a bound-ish token somewhere in the body is not enough.
    guards: Vec<Expr>,
    /// `let <name> = <expr>` bindings, so a guard written against a local
    /// (`let n = self.items.len(); assert!(n < MAX)`) still resolves.
    bindings: HashMap<String, Expr>,
    /// Storage reads the body increments (`self.item_count += 1`), keyed by token
    /// text. This is what makes a field a *counter* structurally, rather than by
    /// its name.
    counters: HashSet<String>,
}

struct FactCollector {
    facts: BodyFacts,
}

impl<'ast> Visit<'ast> for FactCollector {
    fn visit_local(&mut self, l: &'ast syn::Local) {
        if let (syn::Pat::Ident(pi), Some(init)) = (&l.pat, &l.init) {
            self.facts
                .bindings
                .insert(pi.ident.to_string(), (*init.expr).clone());
        }
        syn::visit::visit_local(self, l);
    }

    fn visit_expr_if(&mut self, i: &'ast syn::ExprIf) {
        self.facts.guards.push((*i.cond).clone());
        syn::visit::visit_expr_if(self, i);
    }

    fn visit_expr_while(&mut self, w: &'ast syn::ExprWhile) {
        self.facts.guards.push((*w.cond).clone());
        syn::visit::visit_expr_while(self, w);
    }

    fn visit_expr_binary(&mut self, b: &'ast syn::ExprBinary) {
        if is_assign_op(&b.op) && is_storage_field_read(b.left.as_ref()) {
            self.facts
                .counters
                .insert(b.left.to_token_stream().to_string());
        }
        syn::visit::visit_expr_binary(self, b);
    }

    fn visit_expr_assign(&mut self, a: &'ast syn::ExprAssign) {
        // `self.n = self.n + 1` is the same counter shape as `self.n += 1`.
        if is_storage_field_read(a.left.as_ref()) {
            self.facts
                .counters
                .insert(a.left.to_token_stream().to_string());
        }
        syn::visit::visit_expr_assign(self, a);
    }

    fn visit_expr_macro(&mut self, m: &'ast syn::ExprMacro) {
        collect_macro_guards(&m.mac, &mut self.facts);
        syn::visit::visit_expr_macro(self, m);
    }

    fn visit_stmt_macro(&mut self, s: &'ast syn::StmtMacro) {
        // `assert!(..);` in statement position is a StmtMacro, not an ExprMacro.
        collect_macro_guards(&s.mac, &mut self.facts);
        syn::visit::visit_stmt_macro(self, s);
    }
}

fn collect_macro_guards(mac: &syn::Macro, facts: &mut BodyFacts) {
    if !is_assert_family(&mac.path) {
        return;
    }
    if let Ok(args) = mac.parse_body_with(Punctuated::<Expr, Token![,]>::parse_terminated) {
        facts.guards.extend(args);
    }
}

fn collect_facts(block: &syn::Block) -> BodyFacts {
    let mut c = FactCollector {
        facts: BodyFacts::default(),
    };
    c.visit_block(block);
    c.facts
}

/// Substitute a single-segment local through its `let` binding, one level deep.
fn resolve_local<'e>(expr: &'e Expr, bindings: &'e HashMap<String, Expr>) -> &'e Expr {
    let stripped = strip_expr(expr);
    if let Expr::Path(p) = stripped {
        if p.path.segments.len() == 1 {
            if let Some(bound) = bindings.get(&p.path.segments[0].ident.to_string()) {
                return strip_expr(bound);
            }
        }
    }
    stripped
}

/// `field` is a storage counter this body increments and `bound` is a constant.
fn is_counter_vs_const(field: &Expr, bound: &Expr, counters: &HashSet<String>) -> bool {
    is_storage_field_read(field)
        && counters.contains(&field.to_token_stream().to_string())
        && is_constant_bound(bound)
}

/// True if `expr` is a comparison that actually measures storage against a bound.
/// Two accepted shapes, both requiring the measurement to be a *comparison
/// operand* rather than a token appearing anywhere in the body:
///   (a) `self.items.len()` on either side of the comparison, or
///   (b) a storage counter the body increments compared against a constant
///       (`assert!(self.item_count < ITEM_LIMIT)` alongside `self.item_count += 1`).
fn is_bound_comparison(
    expr: &Expr,
    bindings: &HashMap<String, Expr>,
    counters: &HashSet<String>,
) -> bool {
    match strip_expr(expr) {
        Expr::Binary(b) if is_comparison_op(&b.op) => {
            let l = resolve_local(b.left.as_ref(), bindings);
            let r = resolve_local(b.right.as_ref(), bindings);
            contains_storage_len_call(l)
                || contains_storage_len_call(r)
                || is_counter_vs_const(l, r, counters)
                || is_counter_vs_const(r, l, counters)
        }
        // `a && b`, `a || b` — either conjunct may carry the bound.
        Expr::Binary(b) if matches!(b.op, syn::BinOp::And(_) | syn::BinOp::Or(_)) => {
            is_bound_comparison(&b.left, bindings, counters)
                || is_bound_comparison(&b.right, bindings, counters)
        }
        Expr::Unary(u) => is_bound_comparison(&u.expr, bindings, counters),
        _ => false,
    }
}

/// True if any condition the body enforces is a real bound check.
fn body_enforces_bound(facts: &BodyFacts, extra_counters: &HashSet<String>) -> bool {
    let mut counters = facts.counters.clone();
    counters.extend(extra_counters.iter().cloned());
    facts
        .guards
        .iter()
        .any(|g| is_bound_comparison(g, &facts.bindings, &counters))
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
        siblings: &HashMap<String, &syn::Block>,
        caller_counters: &HashSet<String>,
    ) -> bool {
        for call in body_calls {
            if !expr_base_is_self(call.receiver.as_ref()) {
                continue;
            }
            let name = call.method.to_string();
            if let Some(helper_block) = siblings.get(&name) {
                // The helper is analysed with the same structural rules as the
                // caller. Counter increments may live on either side of the call
                // (`self.n += 1` here, `assert!(self.n < MAX)` in the helper), so
                // the caller's counters are visible to the helper's guards.
                let facts = collect_facts(helper_block);
                if body_enforces_bound(&facts, caller_counters) {
                    return true;
                }
            }
        }
        false
    }

    fn check_method(&mut self, method: &ImplItemFn, siblings: &HashMap<String, &syn::Block>) {
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

        // Structural facts (enforced conditions, let-bindings, counter fields).
        let facts = collect_facts(&method.block);

        // ---- Vec push without bounds check ----
        let storage_push = collector
            .calls
            .iter()
            .any(|c| c.method == "push" && expr_base_is_self(c.receiver.as_ref()));

        if storage_push && takes_mut_self(method) {
            let bounded = body_enforces_bound(&facts, &HashSet::new())
                || self.helper_enforces_bound(&collector.calls, siblings, &facts.counters);
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
                || body_enforces_bound(&facts, &HashSet::new())
                || self.helper_enforces_bound(&collector.calls, siblings, &facts.counters);

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
        let mut siblings: HashMap<String, &syn::Block> = HashMap::new();
        for it in &item_impl.items {
            if let ImplItem::Fn(f) = it {
                siblings.insert(f.sig.ident.to_string(), &f.block);
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

    // ---- MUST-STILL-FLAG regression tests (real vulnerabilities) ----

    // FN regression: the method enforces only a *time* window, but the local
    // holding the deadline is named `time_limit`. The pre-fix vocabulary guard
    // matched the substring "limit" anywhere in the body and silenced the
    // detector, so an unbounded attacker-repeatable push went unreported.
    // A bound check must be a comparison against a length/counter, not a name.
    #[test]
    fn test_still_flags_push_guarded_only_by_time_window() {
        // Mirrors the audit probe verbatim, including the `#[ink::contract] mod`
        // nesting and the `&self` `proposal_count` sibling that calls `.len()`.
        let source = r#"
            #[ink::contract]
            mod governance {
                #[ink(storage)]
                pub struct Governance {
                    owner: AccountId,
                    deadline: u64,
                    proposals: Vec<Proposal>,
                }

                impl Governance {
                    #[ink(constructor)]
                    pub fn new(deadline: u64) -> Self {
                        Self { owner: Self::env().caller(), deadline, proposals: Vec::new() }
                    }

                    #[ink(message)]
                    pub fn submit_proposal(&mut self, text: Vec<u8>) {
                        let time_limit = self.deadline;
                        let now = self.env().block_timestamp();
                        assert!(now < time_limit, "voting window closed");

                        let author = self.env().caller();
                        self.proposals.push(Proposal { author, text, votes: 0 });
                    }

                    #[ink(message)]
                    pub fn proposal_count(&self) -> u32 {
                        self.proposals.len() as u32
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag an unbounded push whose only guard is a time window, \
             regardless of a local named `time_limit`"
        );
    }

    // Same class: bound vocabulary present as a *value computation* rather than
    // an enforced condition. `capacity`/`len()` appear in the body but nothing
    // compares them against a cap before the push.
    #[test]
    fn test_still_flags_push_with_len_used_as_value_only() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn add_item(&mut self, item: u32) {
                    let capacity = self.items.len().checked_sub(1).unwrap_or(0);
                    self.log.push(capacity);
                    self.items.push(item);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag when len()/capacity are only computed, never enforced"
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
