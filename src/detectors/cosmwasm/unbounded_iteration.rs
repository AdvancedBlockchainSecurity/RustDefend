use std::collections::HashSet;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, ExprMethodCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnboundedIterationDetector;

impl Detector for UnboundedIterationDetector {
    fn id(&self) -> &'static str {
        "CW-007"
    }
    fn name(&self) -> &'static str {
        "unbounded-iteration"
    }
    fn description(&self) -> &'static str {
        "Detects .range()/.iter() without .take() in execute handlers"
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
        let mut visitor = IterVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct IterVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// True only for `#[cfg(test)]` exactly. We deliberately do NOT match
/// `#[cfg(not(test))]` (that IS production code) or `#[cfg(feature = "...")]`,
/// so we never suppress an on-chain code path — the safe direction.
fn has_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if !attr.path().is_ident("cfg") {
            return false;
        }
        let toks = attr.meta.to_token_stream().to_string();
        toks.chars().filter(|c| !c.is_whitespace()).collect::<String>() == "cfg(test)"
    })
}

/// Distinguish a cw-storage-plus storage iterator (`Map/IndexedMap/Prefix::range`,
/// signature `range(store, min, max, order)` — always >= 2 args and typically
/// mentions `Order`/`storage`) from an in-memory `std::collections::BTreeMap/BTreeSet::range`,
/// which takes exactly ONE range-expression argument and performs zero storage reads.
///
/// Only storage ranges can exhaust gas via unbounded iteration; in-memory ranges are
/// bounded by the (gas-metered) message payload, so they are never a finding.
fn is_storage_range(call: &ExprMethodCall) -> bool {
    if call.method != "range" {
        return false;
    }
    if call.args.len() >= 2 {
        // cw-storage-plus range takes (store, min, max, order); BTreeMap::range takes one arg.
        return true;
    }
    // Single-arg fallback: only treat as storage range if it clearly references a
    // storage handle / ordering (never true for BTreeMap::range(a..b)).
    let toks = call.args.to_token_stream().to_string();
    toks.contains("Order") || toks.contains("storage")
}

/// A storage `range` call is bounded (constant-gas) if its lazy iterator is consumed
/// by `.take()`, `.next()`, or `.nth()` — the standard peek/pop-front and batch idioms.
fn is_bounding_consumer(name: &str) -> bool {
    name == "take" || name == "next" || name == "nth"
}

/// Stable identity for a call site within one file (the `range` token location).
fn call_key(call: &ExprMethodCall) -> (usize, usize) {
    let span = call.method.span();
    (span.start().line, span.start().column)
}

/// Collect the keys of every storage-range call appearing inside `expr`.
fn storage_range_keys_in(expr: &Expr) -> Vec<(usize, usize)> {
    let mut collector = MethodCallCollector { calls: Vec::new() };
    collector.visit_expr(expr);
    collector
        .calls
        .iter()
        .filter(|c| is_storage_range(c))
        .map(call_key)
        .collect()
}

/// True when both the min and max Bound arguments of a cw range are explicit
/// `Some(Bound::...)` values, i.e. a constrained key window rather than an
/// open-ended `None` scan. Such windows are usually (but not provably) bounded,
/// so we downgrade confidence rather than suppress.
fn has_explicit_bound_window(call: &ExprMethodCall) -> bool {
    let args: Vec<&Expr> = call.args.iter().collect();
    if args.len() < 4 {
        return false;
    }
    let min = args[1].to_token_stream().to_string();
    let max = args[2].to_token_stream().to_string();
    min.contains("Some") && min.contains("Bound") && max.contains("Some") && max.contains("Bound")
}

impl<'ast, 'a> Visit<'ast> for IterVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Never descend into `#[cfg(test)]` modules: their code is excluded from
        // the release wasm artifact and has zero on-chain gas exposure.
        if has_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();
        let is_execute = fn_name.starts_with("execute") || fn_name.starts_with("reply");

        // Skip test functions that happen to start with entry point names.
        let is_test = fn_name.contains("test")
            || fn_name.contains("_works")
            || fn_name.contains("_mock")
            || fn_name.contains("_should")
            || has_attribute(&func.attrs, "test")
            || has_cfg_test(&func.attrs);

        if !is_execute || is_test {
            // Preserve original traversal: only recurse into execute/reply handlers.
            return;
        }

        // Collect every method call in the handler body.
        let mut collector = MethodCallCollector { calls: Vec::new() };
        collector.visit_block(&func.block);

        // Mark storage-range calls whose lazy iterator is consumed by a bounding
        // consumer (take/next/nth) somewhere up its call chain.
        let mut bounded: HashSet<(usize, usize)> = HashSet::new();
        for call in &collector.calls {
            if is_bounding_consumer(&call.method.to_string()) {
                for key in storage_range_keys_in(&call.receiver) {
                    bounded.insert(key);
                }
            }
        }

        // Unbounded storage ranges = storage ranges with no bounding consumer.
        let unbounded: Vec<&ExprMethodCall> = collector
            .calls
            .iter()
            .filter(|c| is_storage_range(c) && !bounded.contains(&call_key(c)))
            .collect();

        if !unbounded.is_empty() {
            // If every unbounded range constrains its key window with explicit
            // Some(Bound::..) min AND max, downgrade to Low confidence (usually
            // bounded, but a caller-controlled window could still be wide).
            let all_windowed = unbounded.iter().all(|c| has_explicit_bound_window(c));
            let (confidence, message) = if all_windowed {
                (
                    Confidence::Low,
                    format!(
                        "Function '{}' uses .range() with an explicit key window but no .take() bound",
                        fn_name
                    ),
                )
            } else {
                (
                    Confidence::Medium,
                    format!("Function '{}' uses .range() without .take() bound", fn_name),
                )
            };

            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "CW-007".to_string(),
                name: "unbounded-iteration".to_string(),
                severity: Severity::High,
                confidence,
                message,
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation:
                    "Add .take(LIMIT) to prevent unbounded iteration that could exceed gas limits"
                        .to_string(),
                chain: Chain::CosmWasm,
            });
        }

        syn::visit::visit_item_fn(self, func);
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
        UnboundedIterationDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unbounded_range() {
        let source = r#"
            fn execute_distribute(deps: DepsMut) -> StdResult<Response> {
                let items: Vec<_> = BALANCES.range(deps.storage, None, None, Order::Ascending).collect::<StdResult<Vec<_>>>()?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect unbounded range");
    }

    #[test]
    fn test_no_finding_with_take() {
        let source = r#"
            fn execute_distribute(deps: DepsMut) -> StdResult<Response> {
                let items: Vec<_> = BALANCES.range(deps.storage, None, None, Order::Ascending).take(100).collect::<StdResult<Vec<_>>>()?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with .take()");
    }

    // FP idx 0: bounded pop-front via .range(...).next() reads exactly one entry.
    #[test]
    fn test_no_finding_range_next_popfront() {
        let source = r#"
            pub fn execute_process_queue(deps: DepsMut, env: Env) -> StdResult<Response> {
                let front = QUEUE
                    .range(deps.storage, None, None, Order::Ascending)
                    .next()
                    .transpose()?;
                if let Some((id, job)) = front {
                    QUEUE.remove(deps.storage, id);
                }
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag .range(...).next() pop-front"
        );
    }

    // FP idx 0 variant: .nth(n) is also a bounded consumer.
    #[test]
    fn test_no_finding_range_nth() {
        let source = r#"
            pub fn execute_peek(deps: DepsMut) -> StdResult<Response> {
                let _ = QUEUE.range(deps.storage, None, None, Order::Ascending).nth(3);
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag .range(...).nth(n)");
    }

    // FP idx 1: std BTreeMap::range over message-derived data (single arg, no storage read).
    #[test]
    fn test_no_finding_btreemap_range() {
        let source = r#"
            pub fn execute_settle(deps: DepsMut, prices: Vec<(u64, Uint128)>, cutoff: u64) -> StdResult<Response> {
                let by_ts: BTreeMap<u64, Uint128> = prices.into_iter().collect();
                let recent: Uint128 = by_ts.range(cutoff..).map(|(_, v)| *v).sum();
                TOTAL.save(deps.storage, &recent)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag in-memory BTreeMap::range"
        );
    }

    // FP idx 2: execute_*-named helper inside a #[cfg(test)] module is never on-chain.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;

                fn execute_and_snapshot(deps: DepsMut) -> Vec<(Addr, Uint128)> {
                    BALANCES
                        .range(deps.storage, None, None, Order::Ascending)
                        .collect::<StdResult<Vec<_>>>()
                        .unwrap()
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag execute_* helper inside #[cfg(test)] module"
        );
    }

    // FP idx 3: explicit Some(Bound::..) key window is downgraded to Low confidence
    // (not suppressed — a caller-controlled window could still be wide).
    #[test]
    fn test_bounded_window_downgraded_to_low() {
        let source = r#"
            const BATCH: u64 = 50;

            pub fn execute_process_batch(deps: DepsMut) -> StdResult<Response> {
                let start = CURSOR.load(deps.storage)?;
                let end = start + BATCH;
                let jobs: Vec<_> = JOBS
                    .range(
                        deps.storage,
                        Some(Bound::inclusive(start)),
                        Some(Bound::exclusive(end)),
                        Order::Ascending,
                    )
                    .collect::<StdResult<Vec<_>>>()?;
                CURSOR.save(deps.storage, &end)?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert_eq!(findings.len(), 1, "Bounded-window range still surfaces");
        assert_eq!(
            findings[0].confidence,
            Confidence::Low,
            "Explicit Some(Bound::..) window should be downgraded to Low confidence"
        );
    }

    // Guard against false negatives: open-ended (None) window keeps Medium confidence.
    #[test]
    fn test_open_range_stays_medium() {
        let source = r#"
            pub fn execute_scan(deps: DepsMut) -> StdResult<Response> {
                let all: Vec<_> = ITEMS
                    .range(deps.storage, None, None, Order::Ascending)
                    .collect::<StdResult<Vec<_>>>()?;
                Ok(Response::new())
            }
        "#;
        let findings = run_detector(source);
        assert_eq!(findings.len(), 1, "Open-ended range must still fire");
        assert_eq!(findings[0].confidence, Confidence::Medium);
    }
}
