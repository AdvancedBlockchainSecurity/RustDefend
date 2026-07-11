use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct PriorityFeeDetector;

impl Detector for PriorityFeeDetector {
    fn id(&self) -> &'static str {
        "SOL-016"
    }
    fn name(&self) -> &'static str {
        "missing-priority-fee"
    }
    fn description(&self) -> &'static str {
        "Detects set_compute_unit_limit without set_compute_unit_price (missing priority fee)"
    }
    fn severity(&self) -> Severity {
        Severity::Low
    }
    fn confidence(&self) -> Confidence {
        Confidence::Low
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Quick check: skip files that don't mention compute budget at all
        if !ctx.source.contains("set_compute_unit_limit")
            && !ctx.source.contains("ComputeBudgetInstruction")
        {
            return Vec::new();
        }

        // File-level check: if a compute-unit-price / priority-fee instruction is
        // handled anywhere in the file, the developer is already dealing with
        // priority fees. Match both the snake_case constructor helper spellings
        // and the CamelCase solana-sdk enum-variant / builder spellings so that
        // e.g. `ComputeBudgetInstruction::SetComputeUnitPrice(..)` is recognized.
        if ctx.source.contains("set_compute_unit_price")
            || ctx.source.contains("compute_unit_price")
            || ctx.source.contains("SetComputeUnitPrice")
            || ctx.source.contains("with_compute_unit_price")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = PriorityFeeVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct PriorityFeeVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for PriorityFeeVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast ItemMod) {
        // Do not descend into `#[cfg(test)]` modules: their helpers and test
        // functions deliberately omit priority fees (there is no fee market on a
        // test validator) and are out of scope for this production-code check.
        if has_cfg_test(&module.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions (including #[tokio::test]/#[async_std::test] etc.)
        // and any function gated to test builds via #[cfg(test)].
        if is_test_fn(func) || has_cfg_test(&func.attrs) {
            return;
        }

        // Require evidence that this function actually *constructs* a compute
        // unit limit instruction. Merely mentioning the `ComputeBudgetInstruction`
        // type (read-only parsers/inspectors that deserialize and pattern-match an
        // existing instruction) or referencing it in a doc comment / log string is
        // not a missing priority fee.
        if !body_constructs_cu_limit(func) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-016".to_string(),
            name: "missing-priority-fee".to_string(),
            severity: Severity::Low,
            confidence: Confidence::Low,
            message: format!(
                "Function '{}' sets compute unit limit without setting compute unit price (priority fee)",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add ComputeBudgetInstruction::set_compute_unit_price() alongside compute unit limit to ensure transaction priority".to_string(),
            chain: Chain::Solana,
        });
    }
}

/// True if the function is a test function: a `test_*` / `*_test` name, or an
/// attribute whose last path segment is `test` (covers `#[test]`,
/// `#[tokio::test]`, `#[async_std::test]`, ...).
fn is_test_fn(func: &ItemFn) -> bool {
    let name = func.sig.ident.to_string();
    if name.starts_with("test_") || name.ends_with("_test") {
        return true;
    }
    func.attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .map_or(false, |seg| seg.ident == "test")
    })
}

/// True if any attribute is `#[cfg(test)]` (or a cfg predicate mentioning test).
fn has_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path().is_ident("cfg") && attr.meta.to_token_stream().to_string().contains("test")
    })
}

/// True if the function body actually constructs a compute-unit-limit
/// instruction (as opposed to merely mentioning the type, matching on it, or
/// documenting it).
fn body_constructs_cu_limit(func: &ItemFn) -> bool {
    // 1. The snake_case constructor helper `set_compute_unit_limit(..)` is
    //    unambiguous: it is always a call and is never a match pattern, so a
    //    token-level check (which also sees inside macros like `vec![..]`) is
    //    sound and preserves detection of the canonical Solana API.
    if fn_body_source(func).contains("set_compute_unit_limit") {
        return true;
    }

    // 2. The CamelCase enum-variant construction
    //    `..::SetComputeUnitLimit(<expr>)` used in *expression* position (an
    //    ExprCall), or built inside a collection macro. Match-arm / `matches!`
    //    patterns are Pat nodes, not ExprCall, and are excluded — that is what
    //    keeps read-only parsers from being flagged.
    let mut visitor = CuLimitConstructionVisitor { found: false };
    visitor.visit_block(&func.block);
    visitor.found
}

struct CuLimitConstructionVisitor {
    found: bool,
}

impl<'ast> Visit<'ast> for CuLimitConstructionVisitor {
    fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
        if let Expr::Path(path_expr) = &*node.func {
            if let Some(seg) = path_expr.path.segments.last() {
                if seg.ident == "SetComputeUnitLimit" {
                    self.found = true;
                }
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_macro(&mut self, node: &'ast syn::Macro) {
        // Collection-building macros (e.g. `vec![Instruction::from(
        // ComputeBudgetInstruction::SetComputeUnitLimit(200_000))]`) hold the
        // construction as raw tokens that syn does not parse into expressions.
        // Treat a variant mention inside a macro as construction, but exclude
        // pattern contexts (`matches!`, or a match written inside a macro, both
        // of which contain `=>` or the `matches` keyword).
        let is_matches = node
            .path
            .segments
            .last()
            .map_or(false, |seg| seg.ident == "matches");
        if !is_matches {
            let toks = node.tokens.to_string();
            if toks.contains("SetComputeUnitLimit")
                && !toks.contains("=>")
                && !toks.contains("matches")
            {
                self.found = true;
            }
        }
        syn::visit::visit_macro(self, node);
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
            Chain::Solana,
            std::collections::HashMap::new(),
        );
        PriorityFeeDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_compute_limit_without_price() {
        let source = r#"
            fn build_transaction(payer: &Keypair) {
                let limit_ix = ComputeBudgetInstruction::set_compute_unit_limit(200_000);
                let instructions = vec![limit_ix, main_instruction];
                let tx = Transaction::new_signed_with_payer(
                    &instructions,
                    Some(&payer.pubkey()),
                    &[payer],
                    recent_blockhash,
                );
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect compute unit limit without price"
        );
        assert_eq!(findings[0].detector_id, "SOL-016");
    }

    #[test]
    fn test_no_finding_with_both_limit_and_price() {
        let source = r#"
            fn build_transaction(payer: &Keypair) {
                let limit_ix = ComputeBudgetInstruction::set_compute_unit_limit(200_000);
                let price_ix = ComputeBudgetInstruction::set_compute_unit_price(1_000);
                let instructions = vec![limit_ix, price_ix, main_instruction];
                let tx = Transaction::new_signed_with_payer(
                    &instructions,
                    Some(&payer.pubkey()),
                    &[payer],
                    recent_blockhash,
                );
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when both limit and price are set"
        );
    }

    // Real detection preserved: CamelCase enum-variant construction of the limit
    // (in expression position) with no price anywhere must still be flagged.
    #[test]
    fn test_detects_camelcase_variant_construction_without_price() {
        let source = r#"
            fn build_budget(payer: &Keypair) {
                let limit_ix = Instruction::from(
                    ComputeBudgetInstruction::SetComputeUnitLimit(200_000),
                );
                let instructions = vec![limit_ix, main_instruction];
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect CamelCase limit construction without price"
        );
        assert_eq!(findings[0].detector_id, "SOL-016");
    }

    // FP #0: both limit and price set via CamelCase solana-sdk enum variants.
    #[test]
    fn test_no_finding_camelcase_price_variant() {
        let source = r#"
            fn build_budget_ixs() -> Vec<Instruction> {
                vec![
                    Instruction::from(ComputeBudgetInstruction::SetComputeUnitLimit(200_000)),
                    Instruction::from(ComputeBudgetInstruction::SetComputeUnitPrice(1_000)),
                ]
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when priority fee is set via SetComputeUnitPrice variant"
        );
    }

    // FP #1: read-only parser/inspector that deserializes and pattern-matches an
    // existing instruction. It constructs nothing and must not be flagged.
    #[test]
    fn test_no_finding_readonly_parser() {
        let source = r#"
            fn extract_cu_limit(data: &[u8]) -> Option<u32> {
                match ComputeBudgetInstruction::try_from_slice(data).ok()? {
                    ComputeBudgetInstruction::SetComputeUnitLimit(units) => Some(units),
                    _ => None,
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Read-only parser matching on the variant must not be flagged"
        );
    }

    // FP #1 variant: `matches!` inspection of an instruction is also read-only.
    #[test]
    fn test_no_finding_matches_inspection() {
        let source = r#"
            fn is_cu_limit(ix: &ComputeBudgetInstruction) -> bool {
                matches!(ix, ComputeBudgetInstruction::SetComputeUnitLimit(_))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "matches! inspection of the variant must not be flagged"
        );
    }

    // FP #3: async integration tests and #[cfg(test)] module helpers.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                #[tokio::test]
                async fn sends_with_budget() {
                    let ix = ComputeBudgetInstruction::set_compute_unit_limit(1_400_000);
                    client.send(&[ix, dummy_ix()]).await.unwrap();
                }

                fn setup_budget_ixs() -> Vec<Instruction> {
                    vec![ComputeBudgetInstruction::set_compute_unit_limit(1_400_000)]
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Test module code (incl. #[tokio::test] and helpers) must not be flagged"
        );
    }

    // FP #4: doc comments / log string literals mentioning the type only.
    #[test]
    fn test_no_finding_doc_comment_mention() {
        let source = r#"
            /// Sends `ixs` as-is. Callers wanting a compute budget must prepend a
            /// ComputeBudgetInstruction themselves.
            fn send_raw(ixs: &[Instruction]) -> Result<Signature> {
                client.send_and_confirm(ixs)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A doc-comment mention of ComputeBudgetInstruction must not be flagged"
        );
    }
}
