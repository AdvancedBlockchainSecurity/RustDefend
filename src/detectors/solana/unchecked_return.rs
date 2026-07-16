use syn::visit::Visit;
use syn::{Expr, ExprCall, Pat, Stmt};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UncheckedReturnDetector;

impl Detector for UncheckedReturnDetector {
    fn id(&self) -> &'static str {
        "SOL-008"
    }
    fn name(&self) -> &'static str {
        "unchecked-cpi-return"
    }
    fn description(&self) -> &'static str {
        "Detects CPI calls whose return value is discarded"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = ReturnVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Returns `true` if `func` is a path expression whose LAST segment is exactly
/// one of the Solana CPI entrypoints. Matching the final path segment (rather
/// than substring-searching the stringified statement) means:
///   * `solana_program::program::invoke(...)` and bare `invoke(...)` both match;
///   * identifiers that merely *contain* "invoke" (`invoker`, `invoke_count`) do
///     NOT match (exact ident comparison);
///   * method calls named `invoke` (`hooks.invoke(ctx)`) are `Expr::MethodCall`,
///     not `Expr::Call`, so they never reach this check;
///   * string literals mentioning "invoke_signed" are never consulted, since we
///     inspect the callee path, not the token text.
fn is_invoke_func(func: &Expr) -> bool {
    if let Expr::Path(path_expr) = func {
        if let Some(seg) = path_expr.path.segments.last() {
            let name = seg.ident.to_string();
            return name == "invoke"
                || name == "invoke_signed"
                || name == "invoke_signed_unchecked";
        }
    }
    false
}

/// Returns `true` for methods that, applied to a CPI `ProgramResult`, provably
/// do NOT handle the error: they either convert it away (`ok`, `err`) or merely
/// inspect it (`is_ok`, `is_err`), yielding a value the caller must still act
/// on. In a dropped position such a chain swallows the error outright, so
/// `invoke(..).ok();` is not meaningfully different from `invoke(..);` — both
/// are the exact bug this detector exists to catch.
///
/// This is deliberately an allowlist keyed on what the method *does*, not a
/// denylist of "handling-looking" names: any method not listed here (`unwrap`,
/// `expect`, `unwrap_or_else`, `map_err`, or anything user-defined) is treated
/// as potential handling and suppresses the finding.
fn is_error_discarding_method(name: &str) -> bool {
    matches!(name, "ok" | "err" | "is_ok" | "is_err")
}

/// If `expr` evaluates a CPI entrypoint (`invoke(...)` / `invoke_signed(...)`)
/// whose `ProgramResult` reaches this position unhandled, returns that call.
///
/// The call may be wrapped in a chain of method calls, but ONLY while every
/// method in the chain is receiver-side and error-discarding
/// (`is_error_discarding_method`) — `invoke(...).ok()` still drops the error,
/// so peeling the chain and flagging it is correct.
///
/// Returns `None` — i.e. does not flag — when the result is genuinely handled
/// or consumed elsewhere:
///   * `invoke(...)?`                  (`Expr::Try` — error propagated)
///   * `invoke(...).unwrap()/.expect()` (method not in the discard allowlist)
///   * `return invoke(...)`            (`Expr::Return` — value propagated)
///   * `results.push(invoke(...))`     (invoke is an *argument*, not the
///                                      receiver, so recursion on the receiver
///                                      `results` bottoms out at `None`)
///   * `assert_cpi_ok(invoke(...))`    (outer `Expr::Call` — result consumed)
///   * `hooks.invoke(ctx)`             (receiver is not a CPI call)
fn as_bare_invoke_call(expr: &Expr) -> Option<&ExprCall> {
    match expr {
        Expr::Call(call) if is_invoke_func(&call.func) => Some(call),
        // Peel the chain only through methods that demonstrably throw the error
        // away, and only via the receiver — a CPI call sitting in argument
        // position is consumed by the enclosing call, not discarded.
        Expr::MethodCall(method_call)
            if is_error_discarding_method(&method_call.method.to_string()) =>
        {
            as_bare_invoke_call(&method_call.receiver)
        }
        _ => None,
    }
}

/// Best-effort real span for a CPI call, anchored on the callee's final path
/// segment ident. Falls back to `call_site` when unavailable.
fn invoke_call_span(call: &ExprCall) -> Span {
    if let Expr::Path(path_expr) = &*call.func {
        if let Some(seg) = path_expr.path.segments.last() {
            return seg.ident.span();
        }
    }
    Span::call_site()
}

struct ReturnVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for ReturnVisitor<'a> {
    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        // `let _ = invoke(...);` — success value discarded with no error handling.
        //
        // Fires when the initializer evaluates an invoke call whose error is
        // still unhandled at this point — including through error-discarding
        // wrappers like `let _ = invoke(...).ok();`. This structurally excludes:
        //   * `let _ = invoke(...)?;`            (Expr::Try — error propagated)
        //   * `let _ = invoke(...).expect(..);`  (Expr::MethodCall — explicit)
        //   * `let _ = invoke(...).unwrap();`    (Expr::MethodCall — explicit)
        //   * `let _ = accounts.invoker.key;`    (Expr::Field — not a CPI call)
        if let Stmt::Local(local) = stmt {
            if let Pat::Wild(_) = &local.pat {
                if let Some(init) = &local.init {
                    if as_bare_invoke_call(&init.expr).is_some() {
                        let line = span_to_line(&local.pat.span());
                        self.findings.push(Finding {
                            detector_id: "SOL-008".to_string(),
                            name: "unchecked-cpi-return".to_string(),
                            severity: Severity::High,
                            confidence: Confidence::High,
                            message: "CPI call result is discarded with `let _ = ...`".to_string(),
                            file: self.ctx.file_path.clone(),
                            line,
                            column: span_to_column(&local.pat.span()),
                            snippet: snippet_at_line(&self.ctx.source, line),
                            recommendation:
                                "Propagate the error using `?` operator: `invoke(...)?.`"
                                    .to_string(),
                            chain: Chain::Solana,
                        });
                    }
                }
            }
        }

        // Bare `invoke(...);` expression statement whose Result is dropped.
        //
        // Fires when the statement's expression evaluates an invoke call whose
        // error is still unhandled — `invoke(...);` and `invoke(...).ok();`
        // alike. This structurally excludes:
        //   * `invoke(...)?;`                 (Expr::Try)
        //   * `return invoke(...);`           (Expr::Return — value propagated)
        //   * `results.push(invoke(...));`    (Expr::MethodCall — result stored)
        //   * `assert_cpi_ok(invoke(...));`   (outer Expr::Call — result consumed)
        //   * `hooks.invoke(ctx);`            (Expr::MethodCall — not a CPI)
        //   * `logger.record("invoke_signed failed", c);` (literal, not a call)
        if let Stmt::Expr(expr, Some(_semi)) = stmt {
            if let Some(call) = as_bare_invoke_call(expr) {
                let span = invoke_call_span(call);
                let line = span_to_line(&span);
                self.findings.push(Finding {
                    detector_id: "SOL-008".to_string(),
                    name: "unchecked-cpi-return".to_string(),
                    severity: Severity::High,
                    confidence: Confidence::High,
                    message: "CPI call result is ignored".to_string(),
                    file: self.ctx.file_path.clone(),
                    line,
                    column: span_to_column(&span),
                    snippet: snippet_at_line(&self.ctx.source, line),
                    recommendation:
                        "Handle the CPI result with `?` operator or explicit error handling"
                            .to_string(),
                    chain: Chain::Solana,
                });
            }
        }

        syn::visit::visit_stmt(self, stmt);
    }
}

use proc_macro2::Span;

trait SpanAccess {
    fn span(&self) -> Span;
}

impl SpanAccess for Pat {
    fn span(&self) -> Span {
        match self {
            Pat::Wild(w) => w.underscore_token.span,
            _ => Span::call_site(),
        }
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
        UncheckedReturnDetector.detect(&ctx)
    }

    // ---- True positives (must keep firing) -------------------------------

    #[test]
    fn test_detects_discarded_result() {
        let source = r#"
            fn do_cpi() {
                let _ = invoke(&instruction, &accounts);
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect discarded CPI result");
    }

    #[test]
    fn test_detects_bare_invoke_statement() {
        let source = r#"
            fn do_cpi() {
                invoke(&instruction, &accounts);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect bare invoke statement with dropped Result"
        );
    }

    #[test]
    fn test_detects_bare_invoke_signed_statement() {
        let source = r#"
            fn do_cpi() {
                invoke_signed(&instruction, &accounts, &seeds);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect bare invoke_signed statement with dropped Result"
        );
    }

    // REGRESSION (false negative): `.ok()` throws the CPI error away just as
    // completely as dropping the Result. ADV-206's guard skipped every
    // Expr::MethodCall wrapper on the theory that a wrapper means "handled",
    // which silenced this genuinely vulnerable pattern. Do not re-broaden the
    // guard to all method calls — key on what the method DOES with the error.
    #[test]
    fn test_still_flags_invoke_signed_result_swallowed_by_ok() {
        let source = r#"
            pub fn settle_loan(
                accounts: &[AccountInfo],
                loan: &mut Loan,
                vault_bump: u8,
            ) -> ProgramResult {
                let vault = &accounts[0];
                let borrower_ata = &accounts[1];
                let seeds: &[&[u8]] = &[b"vault", &[vault_bump]];

                invoke_signed(
                    &ix,
                    &[vault.clone(), borrower_ata.clone()],
                    &[seeds],
                )
                .ok();

                // Runs unconditionally, even when the transfer above reverted.
                loan.outstanding = 0;
                loan.closed = true;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag `invoke_signed(...).ok();` — `.ok()` discards the CPI error"
        );
    }

    // Same discard via the `let _ =` binding form.
    #[test]
    fn test_still_flags_let_wild_invoke_ok() {
        let source = r#"
            fn do_cpi(ix: &Instruction, accounts: &[AccountInfo]) {
                let _ = invoke(ix, accounts).ok();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag `let _ = invoke(...).ok();` (error discarded, not handled)"
        );
    }

    // `is_ok()` in a dropped position inspects the Result without acting on it.
    #[test]
    fn test_still_flags_invoke_is_ok_dropped() {
        let source = r#"
            fn do_cpi(ix: &Instruction, accounts: &[AccountInfo]) {
                invoke(ix, accounts).is_ok();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should flag `invoke(...).is_ok();` (result inspected but never acted on)"
        );
    }

    #[test]
    fn test_no_finding_with_question_mark() {
        let source = r#"
            fn do_cpi() -> Result<(), ProgramError> {
                invoke(&instruction, &accounts)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag when ? is used");
    }

    // ---- False positives (must NOT fire) ---------------------------------

    // idx 0: `let _ = invoke(...)?;` — error already propagated with `?`.
    #[test]
    fn test_no_finding_let_wild_with_question_mark() {
        let source = r#"
            fn do_cpi(ix: &Instruction, accounts: &[AccountInfo]) -> ProgramResult {
                let _ = invoke(ix, accounts)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag `let _ = invoke(...)?;` (error propagated)"
        );
    }

    // idx 0: `let _ = invoke(...).expect(...);` — panic on error is explicit.
    #[test]
    fn test_no_finding_let_wild_with_expect() {
        let source = r#"
            fn do_cpi(ix: &Instruction, accounts: &[AccountInfo]) {
                let _ = invoke(ix, accounts).expect("cpi failed");
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag `let _ = invoke(...).expect(...)` (explicit handling)"
        );
    }

    // idx 1: `return invoke(...);` — result propagated as the return value.
    #[test]
    fn test_no_finding_return_invoke() {
        let source = r#"
            fn process(ix: &Instruction, accounts: &[AccountInfo]) -> ProgramResult {
                if accounts.is_empty() {
                    return Err(ProgramError::NotEnoughAccountKeys);
                }
                return invoke(ix, accounts);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag `return invoke(...);` (result propagated to caller)"
        );
    }

    // idx 2: unrelated `.invoke()` method call and `invoke`-substring identifier.
    #[test]
    fn test_no_finding_unrelated_invoke_method_and_identifier() {
        let source = r#"
            fn run_hooks(hooks: &HookRegistry, ctx: &Ctx) {
                hooks.invoke(ctx);
            }

            fn silence_unused(accounts: &Accounts) {
                let _ = accounts.invoker.key;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag `.invoke()` method calls or `invoker` field access"
        );
    }

    // idx 3: CPI result consumed (stored) by an enclosing call.
    #[test]
    fn test_no_finding_invoke_result_stored() {
        let source = r#"
            fn collect(ix: &Instruction, accounts: &[AccountInfo], results: &mut Vec<ProgramResult>) {
                results.push(invoke(ix, accounts));
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag invoke result stored/consumed by an enclosing call"
        );
    }

    // Boundary of the discard allowlist: peeling stops at the first method that
    // is not provably error-discarding. `.ok().unwrap()` panics on failure, so
    // the error IS acted on and must not be flagged.
    #[test]
    fn test_no_finding_invoke_ok_then_unwrap() {
        let source = r#"
            fn do_cpi(ix: &Instruction, accounts: &[AccountInfo]) {
                invoke(ix, accounts).ok().unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag `invoke(...).ok().unwrap();` (panics on error — handled)"
        );
    }

    // A CPI result whose `is_ok()` is actually consumed by a condition is
    // checked, not discarded — the chain never sits in a dropped position.
    #[test]
    fn test_no_finding_invoke_is_ok_checked_in_condition() {
        let source = r#"
            fn do_cpi(ix: &Instruction, accounts: &[AccountInfo]) -> ProgramResult {
                if invoke(ix, accounts).is_ok() {
                    return Ok(());
                }
                Err(ProgramError::InvalidAccountData)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a CPI result consumed by an `if` condition"
        );
    }

    // idx 4: `invoke_signed` only appears inside a string literal.
    #[test]
    fn test_no_finding_invoke_in_string_literal() {
        let source = r#"
            fn log_failure(logger: &mut Logger, code: u32) {
                logger.record("invoke_signed failed upstream", code);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag CPI names that only appear inside string literals"
        );
    }
}
