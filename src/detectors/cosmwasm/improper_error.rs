use quote::ToTokens;
use syn::visit::Visit;
use syn::{Expr, ExprMethodCall, ItemFn, ItemMod, Macro};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct ImproperErrorDetector;

impl Detector for ImproperErrorDetector {
    fn id(&self) -> &'static str {
        "CW-006"
    }
    fn name(&self) -> &'static str {
        "improper-error-handling"
    }
    fn description(&self) -> &'static str {
        "Detects unwrap(), expect(), panic!() in CosmWasm entry points"
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
        let mut visitor = ErrorVisitor {
            findings: &mut findings,
            ctx,
            current_fn: None,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const ENTRY_POINTS: &[&str] = &[
    "execute",
    "instantiate",
    "query",
    "reply",
    "migrate",
    "sudo",
];

/// True if a function name is a CosmWasm entry point (or a dispatch handler
/// derived from one, e.g. `execute_mint`). Requires an exact match or an
/// underscore word-boundary so accessors like `executed_at`, `queryable_fields`
/// and iterator helpers like `replies` are NOT mistaken for entry points.
fn is_entry_point_name(fn_name: &str) -> bool {
    ENTRY_POINTS
        .iter()
        .any(|ep| fn_name == *ep || fn_name.starts_with(&format!("{}_", ep)))
}

/// True if the attribute list contains a `#[cfg(test)]` (including forms like
/// `#[cfg(all(test, ...))]`). We look for a bare `test` *identifier* token in
/// the cfg predicate, so `#[cfg(feature = "testnet")]` (a string literal) and
/// other production feature gates are NOT matched.
fn cfg_contains_test_ident(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if !attr.path().is_ident("cfg") {
            return false;
        }
        if let syn::Meta::List(list) = &attr.meta {
            token_stream_has_test_ident(list.tokens.clone())
        } else {
            false
        }
    })
}

fn token_stream_has_test_ident(ts: proc_macro2::TokenStream) -> bool {
    use proc_macro2::TokenTree;
    ts.into_iter().any(|tt| match tt {
        TokenTree::Ident(id) => id == "test",
        TokenTree::Group(g) => token_stream_has_test_ident(g.stream()),
        _ => false,
    })
}

/// True if the receiver of an `.unwrap()`/`.expect()` is provably infallible
/// because it is rooted entirely in literals — e.g. `Decimal::from_str("0.003")`
/// or `"123".parse::<u64>()`. Such calls parse compile-time constants: they can
/// only fail deterministically on the very first execution (caught by any test),
/// never on attacker- or chain-state-controlled input. Any receiver that reaches
/// a variable, storage load, query, parameter, or field access returns `false`
/// and stays flagged.
fn receiver_is_literal_infallible(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(_) => true,
        Expr::Paren(p) => receiver_is_literal_infallible(&p.expr),
        Expr::Group(g) => receiver_is_literal_infallible(&g.expr),
        Expr::Reference(r) => receiver_is_literal_infallible(&r.expr),
        Expr::Unary(u) => receiver_is_literal_infallible(&u.expr),
        Expr::Cast(c) => receiver_is_literal_infallible(&c.expr),
        // e.g. `"0.003".parse()` — receiver must be literal-rooted, and any
        // method arguments must themselves be literal-rooted.
        Expr::MethodCall(m) => {
            receiver_is_literal_infallible(&m.receiver)
                && m.args.iter().all(receiver_is_literal_infallible)
        }
        // e.g. `Decimal::from_str("0.003")` — an associated/free function call
        // with a non-empty, fully-literal argument list. Requiring at least one
        // argument avoids suppressing zero-arg calls like `load_config()` that
        // could read global/chain state internally.
        Expr::Call(c) => {
            !c.args.is_empty() && c.args.iter().all(receiver_is_literal_infallible)
        }
        _ => false,
    }
}

struct ErrorVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    current_fn: Option<String>,
}

impl<'ast, 'a> Visit<'ast> for ErrorVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Skip `#[cfg(test)]` modules entirely: their contents (incl. setup
        // helpers like `instantiate_contract`/`execute_mint` that call the real
        // entry points and `.unwrap()` in idiomatic test fashion) are never
        // compiled into the production wasm binary. No true positive lives here.
        if cfg_contains_test_ident(&module.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();
        let is_entry = is_entry_point_name(&fn_name);

        // Skip test functions that happen to start with entry point names
        // e.g., "execute_works", "instantiate_test", "query_balance_test"
        // Skip test helper files entirely
        let file_str = self.ctx.file_path.to_string_lossy();
        if file_str.contains("/testing/")
            || file_str.contains("/tests/")
            || file_str.contains("/testutils/")
            || file_str.contains("helpers.rs")
            || file_str.contains("multitest")
            || file_str.contains("integration_tests")
        {
            return;
        }
        // Mock contracts and non-shipping cargo targets: these are test
        // infrastructure registered with cw-multi-test / examples / benches and
        // never end up in the deployed wasm. `todo!()`/`panic!()` stubs are
        // idiomatic here. Match on path *components* (works with or without a
        // leading slash) to avoid substring false matches like "myexamples".
        if self.ctx.file_path.components().any(|c| {
            matches!(
                c.as_os_str().to_str(),
                Some("mocks") | Some("examples") | Some("benches")
            )
        }) {
            return;
        }
        // A file whose name begins with `mock` (mock.rs, mock_oracle.rs,
        // mock_querier.rs, ...) is, by universal convention, test-only mock
        // infrastructure — production sources are never named this way.
        let file_name = self
            .ctx
            .file_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("");
        if file_name.starts_with("mock") {
            return;
        }

        let is_test = fn_name.contains("test")
            || fn_name.contains("_works")
            || fn_name.contains("_mock")
            || fn_name.contains("_should")
            || fn_name.contains("_helper")
            || fn_name.starts_with("instantiate_with_")
            || has_attribute(&func.attrs, "test")
            || cfg_contains_test_ident(&func.attrs);

        if is_entry && !is_test {
            self.current_fn = Some(fn_name);
            syn::visit::visit_item_fn(self, func);
            self.current_fn = None;
        }
    }

    fn visit_expr_method_call(&mut self, call: &'ast ExprMethodCall) {
        if self.current_fn.is_none() {
            syn::visit::visit_expr_method_call(self, call);
            return;
        }

        let method = call.method.to_string();
        if method == "unwrap" || method == "expect" {
            // Do not flag unwraps/expects whose receiver is a parse of a
            // compile-time constant literal (e.g. `Decimal::from_str("0.003")`).
            // These cannot be triggered by runtime/attacker input.
            if !receiver_is_literal_infallible(&call.receiver) {
                let line = span_to_line(&call.method.span());
                self.findings.push(Finding {
                    detector_id: "CW-006".to_string(),
                    name: "improper-error-handling".to_string(),
                    severity: Severity::High,
                    confidence: Confidence::High,
                    message: format!(
                        "{}() used in entry point '{}'",
                        method,
                        self.current_fn.as_ref().unwrap()
                    ),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&call.method.span()),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation: format!(
                        "Replace .{}() with proper error handling using `?` operator or `.map_err()`",
                        method
                    ),
                    chain: Chain::CosmWasm,
                });
            }
        }

        syn::visit::visit_expr_method_call(self, call);
    }

    fn visit_macro(&mut self, mac: &'ast Macro) {
        if self.current_fn.is_none() {
            return;
        }

        let path_str = mac.path.to_token_stream().to_string();
        if path_str == "panic" || path_str == "todo" || path_str == "unimplemented" {
            let line = span_to_line(&mac.path.segments.first().unwrap().ident.span());
            self.findings.push(Finding {
                detector_id: "CW-006".to_string(),
                name: "improper-error-handling".to_string(),
                severity: Severity::High,
                confidence: Confidence::High,
                message: format!(
                    "{}!() used in entry point '{}'",
                    path_str,
                    self.current_fn.as_ref().unwrap()
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&mac.path.segments.first().unwrap().ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation:
                    "Return a proper error instead of panicking in contract entry points"
                        .to_string(),
                chain: Chain::CosmWasm,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_detector_with_path(source: &str, path: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let ctx = ScanContext::new(
            std::path::PathBuf::from(path),
            source.to_string(),
            ast,
            Chain::CosmWasm,
            std::collections::HashMap::new(),
        );
        ImproperErrorDetector.detect(&ctx)
    }

    fn run_detector(source: &str) -> Vec<Finding> {
        run_detector_with_path(source, "test.rs")
    }

    #[test]
    fn test_detects_unwrap_in_execute() {
        let source = r#"
            fn execute(deps: DepsMut, env: Env, info: MessageInfo, msg: ExecuteMsg) -> StdResult<Response> {
                let val: u64 = some_result.unwrap();
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect unwrap in execute");
    }

    #[test]
    fn test_no_finding_in_test_fn() {
        let source = r#"
            fn instantiate_works() {
                let res = instantiate(deps.as_mut(), mock_env(), info, msg).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag unwrap in test-like functions"
        );
    }

    #[test]
    fn test_no_finding_in_helper() {
        let source = r#"
            fn helper_function() -> u64 {
                some_result.unwrap()
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag unwrap in helper functions"
        );
    }

    // --- FP 0: helper fns inside a #[cfg(test)] module in contract.rs ---
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;

                fn instantiate_contract(deps: DepsMut) -> Response {
                    instantiate(deps, mock_env(), mock_info("creator", &[]), InstantiateMsg { owner: "a".into() }).unwrap()
                }

                fn execute_mint(deps: DepsMut, amount: u128) -> Response {
                    execute(deps, mock_env(), mock_info("minter", &[]), ExecuteMsg::Mint { amount: amount.into() }).unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag unwrap in #[cfg(test)] test-module helpers"
        );
    }

    // --- FP 1: infallible unwrap/expect on constant literals ---
    #[test]
    fn test_no_finding_on_literal_constant_parse() {
        let source = r#"
            pub fn instantiate(deps: DepsMut, _env: Env, _info: MessageInfo, msg: InstantiateMsg) -> Result<Response, ContractError> {
                let default_fee = Decimal::from_str("0.003").unwrap();
                let cap = Uint128::from_str("1000000").expect("constant");
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag unwrap/expect on parses of compile-time constant literals"
        );
    }

    #[test]
    fn test_still_flags_unwrap_on_runtime_receiver() {
        // Guard against over-narrowing FP1: an unwrap on a non-literal
        // (storage/query) receiver must still fire.
        let source = r#"
            pub fn execute(deps: DepsMut, env: Env, info: MessageInfo, msg: ExecuteMsg) -> Result<Response, ContractError> {
                let cfg = CONFIG.load(deps.storage).unwrap();
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag unwrap on storage-load receiver"
        );
    }

    // --- FP 2: prefix over-match on non-entry functions ---
    #[test]
    fn test_no_finding_on_prefix_overmatch() {
        let source = r#"
            fn executed_at(&self) -> Timestamp {
                self.executed_time.expect("executed_time set during execution")
            }
            fn queryable_fields(&self) -> Vec<String> {
                self.fields.clone().expect("fields")
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag expect in functions that merely share an entry-point prefix"
        );
    }

    #[test]
    fn test_still_flags_dispatch_handler() {
        // Guard against over-narrowing FP2: real dispatch handlers derived from
        // an entry point (execute_mint) must still fire.
        let source = r#"
            fn execute_mint(deps: DepsMut, env: Env, info: MessageInfo, msg: ExecuteMsg) -> StdResult<Response> {
                let amount = balances.load(deps.storage).unwrap();
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still flag unwrap in an `execute_`-prefixed dispatch handler"
        );
    }

    // --- FP 4: mock contract files with panicking stubs ---
    #[test]
    fn test_no_finding_in_mock_file() {
        let source = r#"
            pub fn execute(_deps: DepsMut, _env: Env, _info: MessageInfo, _msg: MockMsg) -> StdResult<Response> {
                todo!()
            }
            pub fn query(_deps: Deps, _env: Env, _msg: MockQuery) -> StdResult<Binary> {
                panic!("mock oracle: query not supported in this test")
            }
        "#;
        let findings = run_detector_with_path(source, "src/testing_mocks/mock_oracle.rs");
        assert!(
            findings.is_empty(),
            "Should not flag panicking stubs in mock contract files"
        );
    }

    #[test]
    fn test_no_finding_in_examples_dir() {
        let source = r#"
            pub fn execute(_deps: DepsMut, _env: Env, _info: MessageInfo, _msg: MockMsg) -> StdResult<Response> {
                panic!("example stub")
            }
        "#;
        let findings = run_detector_with_path(source, "examples/schema.rs");
        assert!(
            findings.is_empty(),
            "Should not flag code under examples/ (non-shipping cargo target)"
        );
    }
}
