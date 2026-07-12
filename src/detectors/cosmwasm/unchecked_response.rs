use quote::ToTokens;
use syn::visit::Visit;
use syn::ItemFn;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UncheckedResponseDetector;

impl Detector for UncheckedResponseDetector {
    fn id(&self) -> &'static str {
        "CW-005"
    }
    fn name(&self) -> &'static str {
        "unchecked-query-response"
    }
    fn description(&self) -> &'static str {
        "Detects query responses used without validation"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::Low
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = ResponseVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct ResponseVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// True if a function body (tokenized form, i.e. `func.block.to_token_stream()`)
/// contains an expected-value / bounds check.
///
/// NOTE: `fn_body_source` renders macros with a space before `!`
/// (e.g. `ensure ! ( ... )`, `ensure_eq ! ( ... )`), so the literal substrings
/// "ensure!" / "assert!" can never appear. We therefore match the macro *stems*
/// ("ensure", "assert", "require") which cover `ensure!`, `ensure_eq!`,
/// `ensure_ne!`, `assert!`, `assert_eq!`, `assert_ne!`, `require!` after
/// tokenization, in addition to explicit comparisons / branches.
fn body_has_validation(body_src: &str) -> bool {
    body_src.contains("ensure")
        || body_src.contains("assert")
        || body_src.contains("require")
        || body_src.contains("if ")
        || body_src.contains("match ")
        || body_src.contains(">")
        || body_src.contains("<")
        || body_src.contains("== ")
}

/// Tokenized source of a function's declared return type (empty for `()`).
fn return_type_source(func: &ItemFn) -> String {
    match &func.sig.output {
        syn::ReturnType::Type(_, ty) => ty.to_token_stream().to_string(),
        syn::ReturnType::Default => String::new(),
    }
}

/// True if the body constructs an on-chain message or mutates contract storage.
/// Used to distinguish a pure read-only query relay from a handler that *acts*
/// on the cross-contract response.
fn body_has_state_sink(body_src: &str) -> bool {
    body_src.contains("BankMsg")
        || body_src.contains("WasmMsg")
        || body_src.contains("SubMsg")
        || body_src.contains("CosmosMsg")
        || body_src.contains(". save (")
        || body_src.contains(". update (")
        || body_src.contains(". remove (")
}

/// A read-only query proxy/router: returns a `Binary` payload and merely
/// re-serializes the (already schema-validated, error-propagated) typed
/// response back to the caller without any state write or message construction.
/// Nothing meaningful can be "validated" in such a relay, so it is not a CW-005
/// vulnerability.
fn is_query_relay(func: &ItemFn) -> bool {
    let ret = return_type_source(func);
    if !ret.contains("Binary") {
        return false;
    }
    let body = fn_body_source(func);
    let forwards = body.contains("to_binary") || body.contains("to_json_binary");
    forwards && !body_has_state_sink(&body)
}

/// Collect the names of free functions invoked via a call expression
/// (e.g. `validate_price(&price)`), including the last path segment for
/// `module::func(..)` calls. Method calls are intentionally excluded so we
/// don't pick up `.query_wasm_smart(..)` and friends.
fn collect_called_fn_names(func: &ItemFn) -> Vec<String> {
    struct Collector {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for Collector {
        fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
            if let syn::Expr::Path(p) = node.func.as_ref() {
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
    let mut collector = Collector { names: Vec::new() };
    collector.visit_item_fn(func);
    collector.names
}

/// Resolve a free-function definition by name anywhere in the parsed file and
/// return its tokenized body source, if found.
fn resolve_fn_body(ast: &syn::File, name: &str) -> Option<String> {
    struct Finder<'a> {
        name: &'a str,
        body: Option<String>,
    }
    impl<'ast, 'a> Visit<'ast> for Finder<'a> {
        fn visit_item_fn(&mut self, node: &'ast ItemFn) {
            if self.body.is_none() && node.sig.ident == self.name {
                self.body = Some(fn_body_source(node));
            }
            syn::visit::visit_item_fn(self, node);
        }
    }
    let mut finder = Finder { name, body: None };
    finder.visit_file(ast);
    finder.body
}

/// True if the attribute is `#[cfg(test)]` (or any `cfg(...)` predicate that
/// mentions `test`, e.g. `#[cfg(all(test, ...))]`).
fn attr_is_cfg_test(attr: &syn::Attribute) -> bool {
    if let Some(ident) = attr.path().get_ident() {
        if ident == "cfg" {
            return attr.meta.to_token_stream().to_string().contains("test");
        }
    }
    false
}

impl<'a> ResponseVisitor<'a> {
    /// True if the function delegates validation of the query response to a
    /// helper that we can *resolve* in this file and confirm actually performs a
    /// check. We never skip on the callee name alone — the callee body must be
    /// resolved and contain a real validation token — so unresolved or
    /// non-validating helpers keep the finding (no false negatives).
    fn has_delegated_validation(&self, func: &ItemFn) -> bool {
        for name in collect_called_fn_names(func) {
            if let Some(body) = resolve_fn_body(&self.ctx.ast, &name) {
                if body_has_validation(&body) {
                    return true;
                }
            }
        }
        false
    }
}

impl<'ast, 'a> Visit<'ast> for ResponseVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast syn::ItemMod) {
        // Do not descend into `#[cfg(test)]` modules: their contents are
        // cw-multi-test scaffolding compiled out of the wasm artifact, never
        // production code. This covers inline `#[cfg(test)] mod tests { .. }`
        // helper fns (e.g. `query_balance`, `setup`) that the name/path
        // skip-lists miss.
        if node.attrs.iter().any(attr_is_cfg_test) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions
        if fn_name.contains("test")
            || fn_name.ends_with("_works")
            || fn_name.starts_with("mock_")
            || fn_name.contains("_mock")
            || has_attribute(&func.attrs, "test")
        {
            return;
        }

        // Skip test helper files
        let file_str = self.ctx.file_path.to_string_lossy();
        if file_str.contains("/testing/")
            || file_str.contains("/tests/")
            || file_str.contains("/testutils/")
            || file_str.contains("integration_tests")
            || file_str.contains("helpers.rs")
            || file_str.contains("multitest")
        {
            return;
        }

        let body_src = fn_body_source(func);

        // Look for querier usage
        if !body_src.contains("querier") && !body_src.contains("query_wasm") {
            return;
        }

        // Check for direct query response usage without validation
        let has_query = body_src.contains(".query(") || body_src.contains("query_wasm_smart");

        if !has_query {
            return;
        }

        // Check if response is validated within this function body.
        if body_has_validation(&body_src) {
            return;
        }

        // Read-only query proxy/router that just relays a typed response as
        // Binary: nothing to validate, no state/fund sink.
        if is_query_relay(func) {
            return;
        }

        // Validation factored into a resolvable helper called via `?`.
        if self.has_delegated_validation(func) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "CW-005".to_string(),
            name: "unchecked-query-response".to_string(),
            severity: Severity::High,
            confidence: Confidence::Low,
            message: format!(
                "Function '{}' uses query response without validation",
                func.sig.ident
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation:
                "Validate query responses before using them (check bounds, expected values, etc.)"
                    .to_string(),
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
        UncheckedResponseDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unchecked_response() {
        let source = r#"
            fn get_price(deps: Deps) -> StdResult<Uint128> {
                let price: PriceResponse = deps.querier.query_wasm_smart(oracle, &msg)?;
                Ok(price.amount)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect unchecked query response"
        );
    }

    #[test]
    fn test_no_finding_with_validation() {
        let source = r#"
            fn get_price(deps: Deps) -> StdResult<Uint128> {
                let price: PriceResponse = deps.querier.query_wasm_smart(oracle, &msg)?;
                if price.amount > Uint128::zero() {
                    Ok(price.amount)
                } else {
                    Err(StdError::generic_err("invalid price"))
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with validation");
    }

    // FP idx 0: ensure_eq!/ensure! validation not recognized because the
    // tokenized body renders the macro as `ensure_eq ! ( ... )`.
    #[test]
    fn test_no_finding_with_ensure_eq() {
        let source = r#"
            fn assert_owner(deps: Deps, sender: Addr) -> StdResult<()> {
                let owner: Addr = deps.querier.query_wasm_smart(registry, &QueryMsg::Owner {})?;
                ensure_eq!(owner, sender, StdError::generic_err("unauthorized"));
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "ensure_eq! validation should be recognized"
        );
    }

    // FP idx 1: validation delegated to a resolvable helper via `?` propagation.
    #[test]
    fn test_no_finding_with_delegated_validation() {
        let source = r#"
            fn get_price(deps: Deps) -> StdResult<Uint128> {
                let price: PriceResponse = deps.querier.query_wasm_smart(oracle, &msg)?;
                validate_price(&price)?;
                Ok(price.amount)
            }

            fn validate_price(p: &PriceResponse) -> StdResult<()> {
                ensure!(!p.amount.is_zero(), StdError::generic_err("zero price"));
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Delegated validation in a resolvable helper should be recognized"
        );
    }

    // Soundness guard for FP idx 1: a helper that does NOT actually validate
    // must not suppress the finding (no false negative).
    #[test]
    fn test_flags_when_helper_does_not_validate() {
        let source = r#"
            fn get_price(deps: Deps) -> StdResult<Uint128> {
                let price: PriceResponse = deps.querier.query_wasm_smart(oracle, &msg)?;
                log_price(&price);
                Ok(price.amount)
            }

            fn log_price(p: &PriceResponse) {
                let _ = p;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A non-validating helper must not suppress the finding"
        );
    }

    // FP idx 2: read-only query relay that forwards a typed response as Binary.
    #[test]
    fn test_no_finding_query_relay_binary() {
        let source = r#"
            fn query_pair_config(deps: Deps) -> StdResult<Binary> {
                let cfg: ConfigResponse = deps.querier.query_wasm_smart(factory, &FactoryQuery::Config {})?;
                to_binary(&cfg)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Read-only Binary relay should not be flagged"
        );
    }

    // FP idx 3: non-#[test] helper functions inside an inline #[cfg(test)] module.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;

                fn query_balance(app: &App, user: &Addr) -> Uint128 {
                    let res: BalanceResponse = app
                        .wrap()
                        .query_wasm_smart(CONTRACT.clone(), &QueryMsg::Balance { addr: user.clone() })
                        .unwrap();
                    res.amount
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Helpers inside #[cfg(test)] modules should not be flagged"
        );
    }
}
