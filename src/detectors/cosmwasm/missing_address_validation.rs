use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, ExprCall, ExprMethodCall, ItemFn, ItemMod, Lit};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingAddressValidationDetector;

impl Detector for MissingAddressValidationDetector {
    fn id(&self) -> &'static str {
        "CW-009"
    }
    fn name(&self) -> &'static str {
        "cosmwasm-missing-addr-validation"
    }
    fn description(&self) -> &'static str {
        "Detects Addr::unchecked() usage in non-test code (address validation bypass)"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::CosmWasm
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = AddrVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct AddrVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// True if `attrs` contains a `#[cfg(test)]` (or `#[cfg(all(test, ...))]`) attribute.
///
/// Intentionally does NOT match `#[cfg(not(test))]` (production code) or feature
/// predicates that merely contain the substring "test": we normalize the token
/// stream and require the predicate to be exactly `test` (or an `all(...)` group
/// whose first predicate is `test`). This keeps us from silencing real, non-test
/// code that happens to mention "test" in a cfg.
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if attr.path().is_ident("cfg") {
            let tokens = attr.meta.to_token_stream().to_string();
            let norm: String = tokens.split_whitespace().collect();
            return norm == "cfg(test)" || norm.starts_with("cfg(all(test");
        }
        false
    })
}

/// True if the call expression is `Addr::unchecked(...)` (allowing a fully
/// qualified path such as `cosmwasm_std::Addr::unchecked`).
fn is_addr_unchecked_call(node: &ExprCall) -> bool {
    if let Expr::Path(expr_path) = node.func.as_ref() {
        let segs: Vec<String> = expr_path
            .path
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect();
        let n = segs.len();
        return n >= 2 && segs[n - 1] == "unchecked" && segs[n - 2] == "Addr";
    }
    false
}

/// True if a path plausibly refers to a `const`/`static` item, using the
/// SCREAMING_SNAKE_CASE convention (all upper-case ASCII, at least one letter).
/// Attacker-controlled inputs arrive through lower-case parameters / message
/// fields, so a constant-only argument has no case-variation attack surface.
fn path_is_const(path: &syn::Path) -> bool {
    if let Some(seg) = path.segments.last() {
        let name = seg.ident.to_string();
        let has_alpha = name.chars().any(|c| c.is_ascii_alphabetic());
        let all_upper = name
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_');
        return has_alpha && all_upper;
    }
    false
}

/// True if the argument expression is a string literal or a reference to a
/// compile-time constant. Conservative: anything not clearly literal/const is
/// treated as dynamic (i.e. still flagged), so we never mask a real bypass.
fn arg_is_literal_or_const(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(lit) => matches!(lit.lit, Lit::Str(_) | Lit::ByteStr(_)),
        Expr::Reference(r) => arg_is_literal_or_const(r.expr.as_ref()),
        Expr::Group(g) => arg_is_literal_or_const(g.expr.as_ref()),
        Expr::Paren(p) => arg_is_literal_or_const(p.expr.as_ref()),
        Expr::Path(p) => path_is_const(&p.path),
        _ => false,
    }
}

/// True if every argument of this `Addr::unchecked` call is a literal or const.
fn call_is_constant_only(node: &ExprCall) -> bool {
    !node.args.is_empty() && node.args.iter().all(arg_is_literal_or_const)
}

/// Collects all `Addr::unchecked(...)` call expressions in a subtree.
struct UncheckedCallCollector {
    calls: Vec<ExprCall>,
}

impl<'ast> Visit<'ast> for UncheckedCallCollector {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if is_addr_unchecked_call(node) {
            self.calls.push(node.clone());
        }
        syn::visit::visit_expr_call(self, node);
    }
}

/// True if the function body performs a storage mutation (`.save`/`.update`/
/// `.remove`). Used together with the signature check to identify read-only
/// query handlers, which cannot be an address-validation-bypass point.
fn body_mutates(func: &ItemFn) -> bool {
    struct M {
        found: bool,
    }
    impl<'ast> Visit<'ast> for M {
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            let m = node.method.to_string();
            if m == "save" || m == "update" || m == "remove" {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, node);
        }
    }
    let mut m = M { found: false };
    m.visit_block(&func.block);
    m.found
}

impl<'ast, 'a> Visit<'ast> for AddrVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Do not descend into `#[cfg(test)] mod ...`: those items are compiled
        // only into test binaries, never into the deployed contract wasm.
        // Addr::unchecked on literal test addresses there is the standard
        // cw-multi-test bootstrap pattern (e.g. helper `proper_instantiate`).
        if is_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions and mock/helper/setup functions
        if fn_name.starts_with("test_")
            || fn_name.ends_with("_test")
            || fn_name.contains("_works")
            || fn_name.contains("_mock")
            || fn_name.contains("_should")
            || fn_name.starts_with("mock_")
            || fn_name.starts_with("setup")
            || fn_name.starts_with("fixture")
            || fn_name.starts_with("helper")
            || fn_name.starts_with("create_test")
            || fn_name.starts_with("make_test")
            || fn_name.starts_with("default_")
            || fn_name.starts_with("new_test")
            || fn_name.starts_with("instantiate_test")
            || fn_name.contains("mock_deps")
            || fn_name.contains("mock_env")
            || fn_name.contains("mock_info")
            || has_attribute(&func.attrs, "test")
            || is_cfg_test(&func.attrs)
        {
            return;
        }

        // Skip if file path suggests test/mock code, or is a Cargo integration
        // test / example / bench target. Files under tests/, examples/ and
        // benches/ are compiled only as separate test/example binaries and are
        // never linked into the contract artifact; contract source lives in src/.
        let file_str = self.ctx.file_path.to_string_lossy();
        if file_str.contains("/testing")
            || file_str.contains("/mock")
            || file_str.contains("/helpers")
            || file_str.contains("/testutils")
            || file_str.contains("_mock.rs")
            || file_str.contains("_helpers.rs")
            || file_str.contains("test_utils")
            || file_str.contains("testing.rs")
            || file_str.contains("integration_tests")
            || file_str.contains("multitest")
            || file_str.contains("/tests/")
            || file_str.starts_with("tests/")
            || file_str.contains("/examples/")
            || file_str.starts_with("examples/")
            || file_str.contains("/benches/")
            || file_str.starts_with("benches/")
        {
            return;
        }

        // Locate the actual Addr::unchecked(...) call sites (AST, not substring).
        let mut collector = UncheckedCallCollector { calls: Vec::new() };
        collector.visit_block(&func.block);
        if collector.calls.is_empty() {
            return;
        }

        let body_src = fn_body_source(func);

        // Check if there's also addr_validate in the same function (mixed usage is OK)
        if body_src.contains("addr_validate") {
            return;
        }

        // Read-only query handlers: functions taking immutable `Deps` (never
        // `DepsMut`) and performing no storage mutation cannot be a validation
        // bypass point — the string was validated on the write path and is only
        // reconstructed for a query response. The enforcement point is the
        // writer (instantiate/execute), which takes DepsMut and is still flagged.
        let sig_str = func.sig.to_token_stream().to_string();
        let takes_deps_mut = sig_str.contains("DepsMut");
        let takes_immutable_deps = sig_str.contains("Deps") && !takes_deps_mut;
        if takes_immutable_deps && !body_mutates(func) {
            return;
        }

        // Constant/literal-only calls: if every Addr::unchecked call in the
        // function wraps only string literals or SCREAMING_SNAKE_CASE consts
        // (sentinel/burn addresses etc.), there is no attacker-controlled input
        // and no case-variation surface. If ANY call takes a dynamic argument,
        // we still flag the function.
        let has_dynamic_call = collector.calls.iter().any(|c| !call_is_constant_only(c));
        if !has_dynamic_call {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "CW-009".to_string(),
            name: "cosmwasm-missing-addr-validation".to_string(),
            severity: Severity::High,
            confidence: Confidence::Medium,
            message: format!(
                "Function '{}' uses Addr::unchecked() without addr_validate()",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Use deps.api.addr_validate(&addr)? instead of Addr::unchecked() to prevent address case-variation attacks".to_string(),
            chain: Chain::CosmWasm,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_detector(source: &str) -> Vec<Finding> {
        run_detector_with_path(source, "test.rs")
    }

    fn run_detector_with_path(source: &str, path: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let ctx = ScanContext::new(
            std::path::PathBuf::from(path),
            source.to_string(),
            ast,
            Chain::CosmWasm,
            std::collections::HashMap::new(),
        );
        MissingAddressValidationDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unchecked_addr() {
        let source = r#"
            fn execute_transfer(deps: DepsMut, recipient: String) -> StdResult<Response> {
                let addr = Addr::unchecked(&recipient);
                BALANCES.save(deps.storage, &addr, &amount)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect Addr::unchecked");
    }

    #[test]
    fn test_no_finding_with_validation() {
        let source = r#"
            fn execute_transfer(deps: DepsMut, recipient: String) -> StdResult<Response> {
                let addr = deps.api.addr_validate(&recipient)?;
                BALANCES.save(deps.storage, &addr, &amount)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with addr_validate");
    }

    #[test]
    fn test_no_finding_in_test() {
        let source = r#"
            #[test]
            fn test_transfer() {
                let addr = Addr::unchecked("sender");
                assert_eq!(addr, expected);
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag in test functions");
    }

    #[test]
    fn test_no_finding_in_mock_function() {
        let source = r#"
            fn mock_deps() -> OwnedDeps<MockStorage> {
                let addr = Addr::unchecked("contract_addr");
                mock_dependencies()
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag mock/helper functions");
    }

    #[test]
    fn test_no_finding_in_setup_function() {
        let source = r#"
            fn setup_contract(deps: DepsMut) {
                let addr = Addr::unchecked("admin");
                CONFIG.save(deps.storage, &addr).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag setup functions");
    }

    // ---- FP regression tests (v0.5.x false-positive reduction) ----

    // idx 0: non-#[test] helper inside a #[cfg(test)] module must not be flagged.
    #[test]
    fn test_no_finding_cfg_test_module_helper() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;

                fn proper_instantiate(app: &mut App, owner_name: String) -> Addr {
                    let owner = Addr::unchecked(owner_name);
                    owner
                }

                #[test]
                fn works() {
                    let mut app = App::default();
                    let _ = proper_instantiate(&mut app, "owner".to_string());
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag helpers inside a #[cfg(test)] module"
        );
    }

    // idx 1: top-level helper in a Cargo integration-test file (tests/) must not
    // be flagged, even with a dynamic argument.
    #[test]
    fn test_no_finding_in_integration_tests_dir() {
        let source = r#"
            fn admin(name: String) -> Addr {
                Addr::unchecked(name)
            }
        "#;
        let findings = run_detector_with_path(source, "tests/contract_flow.rs");
        assert!(
            findings.is_empty(),
            "Should not flag helpers in the crate-root tests/ directory"
        );
    }

    // idx 3: read-only query handler taking immutable Deps must not be flagged.
    #[test]
    fn test_no_finding_read_only_query() {
        let source = r#"
            fn query_config(deps: Deps) -> StdResult<ConfigResponse> {
                let cfg = CONFIG.load(deps.storage)?;
                Ok(ConfigResponse {
                    owner: Addr::unchecked(cfg.owner),
                })
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag read-only query handlers over trusted storage"
        );
    }

    // idx 4: Addr::unchecked on a compile-time constant must not be flagged.
    #[test]
    fn test_no_finding_constant_argument() {
        let source = r#"
            const BURN_ADDRESS: &str = "cosmos1burnburnburnburnburnburnburnxqp2c0k";

            fn burn_target() -> Addr {
                Addr::unchecked(BURN_ADDRESS)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag Addr::unchecked on a compile-time constant"
        );
    }

    // Guard soundness: a mutating execute handler with a dynamic argument must
    // STILL be flagged even though it also constructs a constant address.
    #[test]
    fn test_still_flags_mixed_constant_and_dynamic() {
        let source = r#"
            fn execute_route(deps: DepsMut, recipient: String) -> StdResult<Response> {
                let sentinel = Addr::unchecked(BURN_ADDRESS);
                let addr = Addr::unchecked(recipient);
                BALANCES.save(deps.storage, &addr, &amount)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Must still flag a dynamic Addr::unchecked even alongside a constant one"
        );
    }
}
