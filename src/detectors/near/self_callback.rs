use syn::visit::Visit;
use syn::ItemFn;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct SelfCallbackDetector;

impl Detector for SelfCallbackDetector {
    fn id(&self) -> &'static str {
        "NEAR-007"
    }
    fn name(&self) -> &'static str {
        "self-callback-state"
    }
    fn description(&self) -> &'static str {
        "Detects pending state field writes before ext_self:: calls without guard checks"
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
        let mut findings = Vec::new();
        let mut visitor = SelfCallbackVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct SelfCallbackVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for SelfCallbackVisitor<'a> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // #[private] / #[callback] methods can only be invoked by the contract
        // itself (near_bindgen restricts them to env::current_account_id()), so
        // an external actor cannot re-enter them to race the pending state.
        // Setting/clearing in-flight state inside such a callback is the exact
        // remediation this detector recommends, not the vulnerability. Skipping
        // them cannot hide a true positive of this class (which is about an
        // *externally* reachable entry point setting pending state unguarded).
        if has_attribute(&func.attrs, "private") || has_attribute(&func.attrs, "callback") {
            return;
        }

        let body_src = fn_body_source(func);

        // Must have ext_self call
        if !body_src.contains("ext_self") {
            return;
        }

        // Must actually WRITE a `self.pending*` state field before the
        // cross-contract call. This is verified against the parsed AST rather
        // than by matching three independent substrings ("pending_", "self .",
        // "="). The old heuristic fired on read-only access (`let amount =
        // self.pending_amount;` — the "=" came from the `let`), on unrelated
        // "==" / "=>" tokens, and on locals merely named `pending_*` (e.g.
        // `let pending_rewards = self.compute_rewards();`). None of those write
        // any in-flight contract state, so none can be observed half-set by a
        // callback.
        if !writes_self_pending_field(func) {
            return;
        }

        // Check for guard (tokenized form has space: "assert !")
        let has_guard = body_src.contains("assert !")
            || body_src.contains("assert!")
            || body_src.contains("require !")
            || body_src.contains("require!")
            || body_src.contains("if self . pending")
            || body_src.contains("if self.pending");

        if !has_guard {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "NEAR-007".to_string(),
                name: "self-callback-state".to_string(),
                severity: Severity::High,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' sets pending state before ext_self callback without guard",
                    func.sig.ident
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Add a guard check for pending state (e.g., assert!(!self.pending_withdrawal)) before setting it, and clear it in the callback".to_string(),
                chain: Chain::Near,
            });
        }
    }
}

/// Returns true if the function body contains an assignment (`=` or a compound
/// assign such as `+=`) whose left-hand side is a field-access chain rooted at
/// `self` where the field taken directly off `self` has a name starting with
/// "pending" — e.g. `self.pending_amount = amount;` or
/// `self.pending_state.step = 1;`.
///
/// This distinguishes a genuine in-flight state write from a `let` binding, an
/// `==` comparison, a `=>` match arm, or a local variable named `pending_*`,
/// all of which satisfied the old substring heuristic but write no contract
/// state.
fn writes_self_pending_field(func: &ItemFn) -> bool {
    struct WriteVisitor {
        found: bool,
    }

    impl<'ast> Visit<'ast> for WriteVisitor {
        fn visit_expr_assign(&mut self, node: &'ast syn::ExprAssign) {
            if lhs_is_self_pending(&node.left) {
                self.found = true;
            }
            syn::visit::visit_expr_assign(self, node);
        }

        fn visit_expr_binary(&mut self, node: &'ast syn::ExprBinary) {
            use syn::BinOp::*;
            let is_compound_assign = matches!(
                node.op,
                AddAssign(_)
                    | SubAssign(_)
                    | MulAssign(_)
                    | DivAssign(_)
                    | RemAssign(_)
                    | BitXorAssign(_)
                    | BitAndAssign(_)
                    | BitOrAssign(_)
                    | ShlAssign(_)
                    | ShrAssign(_)
            );
            if is_compound_assign && lhs_is_self_pending(&node.left) {
                self.found = true;
            }
            syn::visit::visit_expr_binary(self, node);
        }
    }

    let mut v = WriteVisitor { found: false };
    v.visit_block(&func.block);
    v.found
}

/// Walk a field-access chain and return true if it is rooted at `self` and the
/// field accessed directly off `self` has a name starting with "pending".
fn lhs_is_self_pending(expr: &syn::Expr) -> bool {
    if let syn::Expr::Field(field) = expr {
        if expr_is_self(&field.base) {
            if let syn::Member::Named(ident) = &field.member {
                return ident.to_string().starts_with("pending");
            }
            return false;
        }
        // e.g. `self.pending_state.foo` — recurse toward the `self` root.
        return lhs_is_self_pending(&field.base);
    }
    false
}

/// True if `expr` is exactly the `self` receiver.
fn expr_is_self(expr: &syn::Expr) -> bool {
    if let syn::Expr::Path(path_expr) = expr {
        return path_expr.qself.is_none() && path_expr.path.is_ident("self");
    }
    false
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
        SelfCallbackDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unguarded_pending() {
        let source = r#"
            fn initiate_withdrawal(&mut self, amount: u128) {
                self.pending_amount = amount;
                ext_self::on_withdrawal_complete(env::current_account_id(), 0, GAS);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect unguarded pending state"
        );
    }

    #[test]
    fn test_no_finding_with_guard() {
        let source = r#"
            fn initiate_withdrawal(&mut self, amount: u128) {
                assert!(!self.pending_withdrawal, "Already pending");
                self.pending_amount = amount;
                ext_self::on_withdrawal_complete(env::current_account_id(), 0, GAS);
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with guard");
    }

    // FP idx 0: read-only access to pending state must not be treated as a
    // write. The `=` comes from the `let` binding, not an assignment to
    // self.pending_*.
    #[test]
    fn test_no_finding_read_only_pending() {
        let source = r#"
            pub fn retry_withdrawal(&mut self) -> Promise {
                let amount = self.pending_amount;
                ext_self::on_withdrawal_complete(env::current_account_id(), 0, GAS)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Read-only access to pending state must not be flagged"
        );
    }

    // FP idx 1: #[private] callback that clears pending state and chains the
    // next promise step is the prescribed remediation, not a vulnerability.
    #[test]
    fn test_no_finding_private_callback() {
        let source = r#"
            #[private]
            pub fn on_withdrawal_complete(&mut self) {
                self.pending_amount = 0;
                ext_self::finalize_withdrawal(env::current_account_id(), 0, GAS);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "#[private] callbacks cannot be externally re-entered"
        );
    }

    // FP idx 3: a local variable named pending_* writes no contract state.
    #[test]
    fn test_no_finding_local_named_pending() {
        let source = r#"
            pub fn distribute(&mut self) -> Promise {
                let pending_rewards = self.compute_rewards();
                ext_self::on_distribute(env::current_account_id(), 0, GAS)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A local named pending_* is not a pending state write"
        );
    }
}
