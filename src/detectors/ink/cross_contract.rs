use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;

use std::collections::HashSet;
use syn::visit::Visit;

pub struct CrossContractDetector;

impl Detector for CrossContractDetector {
    fn id(&self) -> &'static str {
        "INK-006"
    }
    fn name(&self) -> &'static str {
        "ink-cross-contract"
    }
    fn description(&self) -> &'static str {
        "Detects try_invoke() without result check"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Ink
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();

        // AST-confirmed call sites: lines that contain a real `.try_invoke(...)`
        // method call. This excludes comments, doc comments, and string literals
        // that merely mention the identifier (FP idx 1).
        let ast_call_lines = collect_try_invoke_call_lines(&ctx.ast);

        let lines: Vec<&str> = ctx.source.lines().collect();

        for (line_idx, raw_line) in lines.iter().enumerate() {
            let line_num = line_idx + 1;

            // Analyse only the code portion of the line (drop trailing comments)
            // so tokens inside comments never mask or manufacture a match.
            let stripped = strip_line_comment(raw_line);

            // A line is a genuine call site only if the AST saw a `try_invoke`
            // method call there, OR the code text literally contains the method
            // call syntax `.try_invoke(` (fallback for calls hidden inside
            // macro token streams that syn does not descend into). Comments and
            // string-only mentions satisfy neither condition.
            let is_call_site =
                ast_call_lines.contains(&line_num) || stripped.contains(".try_invoke(");
            if !is_call_site {
                continue;
            }

            let trimmed = stripped.trim();

            // FP idx 4: the call is in return position (tail expression or an
            // explicit `return`). The full Result is delegated to the caller, which
            // must handle it (Result is #[must_use]). A truly unchecked call is a
            // statement ending in `;` whose value is dropped, so this preserves
            // all real bugs.
            if is_return_position(trimmed) {
                continue;
            }

            // Result handling tokens present on the call line itself
            // (`?`, match, unwrap*, expect, is_ok/is_err, and_then, .ok()/.err()/
            // .map()/map_err) -- FP idx 2.
            let is_handled = has_handler_token(stripped);

            // Immediately-following line handles the result.
            let next_line_handled = lines
                .get(line_idx + 1)
                .map(|l| {
                    let s = strip_line_comment(l);
                    s.contains("match") || s.contains("if let") || s.contains('?')
                })
                .unwrap_or(false);

            // FP idx 3: `let <ident> = ...try_invoke();` whose binding is consumed
            // by a handling construct further down the function (blank lines,
            // comments, or log statements may separate the call from the check).
            // A binding that is never consumed stays flagged.
            let binding_checked = let_binding_ident(stripped)
                .map(|id| ident_checked_in_window(&id, &lines, line_idx + 1, 16))
                .unwrap_or(false);

            // `let _ = ...try_invoke();` discards the result. This is only a bug
            // when no handler token is present (FP idx 0: `let _ = c.try_invoke()?`
            // still propagates errors via `?`). The discard check is anchored so
            // `let _result = ...` is NOT treated as a discard.
            let is_discarded = is_discard_binding(stripped);

            let unhandled = !is_handled && !next_line_handled && !binding_checked;

            if unhandled || (is_discarded && !is_handled) {
                findings.push(Finding {
                    detector_id: "INK-006".to_string(),
                    name: "ink-cross-contract".to_string(),
                    severity: Severity::High,
                    confidence: Confidence::High,
                    message: "try_invoke() result is not checked".to_string(),
                    file: ctx.file_path.clone(),
                    line: line_num,
                    column: 1,
                    snippet: raw_line.trim().to_string(),
                    recommendation:
                        "Handle the try_invoke() result with `?` operator or match on Ok/Err"
                            .to_string(),
                    chain: Chain::Ink,
                });
            }
        }

        findings
    }
}

/// Collect the 1-based source lines on which a real `try_invoke` method call
/// occurs. Comments and string literals never appear here because syn only
/// yields `ExprMethodCall` nodes for actual calls.
fn collect_try_invoke_call_lines(file: &syn::File) -> HashSet<usize> {
    struct Collector {
        lines: HashSet<usize>,
    }
    impl<'ast> Visit<'ast> for Collector {
        fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
            if node.method == "try_invoke" {
                self.lines.insert(node.method.span().start().line);
            }
            syn::visit::visit_expr_method_call(self, node);
        }
    }
    let mut collector = Collector {
        lines: HashSet::new(),
    };
    collector.visit_file(file);
    collector.lines
}

/// Return the code portion of a source line, dropping any `//` line comment.
/// Naive with respect to `//` inside string literals, but adequate: it is only
/// used to avoid treating comment text as code, and AST confirmation covers the
/// rare case of a real call preceding an in-string `//`.
fn strip_line_comment(line: &str) -> &str {
    match line.find("//") {
        Some(idx) => &line[..idx],
        None => line,
    }
}

fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Whether the call line already consumes the Result with a recognised handler.
fn has_handler_token(line: &str) -> bool {
    line.contains('?')
        || line.contains("match")
        || line.contains("unwrap")
        || line.contains("expect")
        || line.contains("if let")
        || line.contains("map_err")
        || line.contains("is_ok")
        || line.contains("is_err")
        || line.contains("and_then")
        || line.contains(".ok(")
        || line.contains(".err(")
        || line.contains(".map(")
}

/// True when the call is a tail expression or explicit `return`, i.e. the whole
/// Result is delegated to the caller.
fn is_return_position(trimmed: &str) -> bool {
    let t = trimmed.trim_end();
    if t == "return" || t.starts_with("return ") {
        return true;
    }
    // Tail expression: a call ending without a trailing `;` is the value of the
    // enclosing block and is returned to the caller.
    t.ends_with(".try_invoke()")
}

/// Detect a `let _ = ...` discard binding (underscore only), not `let _result`.
fn is_discard_binding(line: &str) -> bool {
    let rest = match line.trim_start().strip_prefix("let") {
        Some(r) => r,
        None => return false,
    };
    // `let` must be a whole keyword.
    if !rest.starts_with(char::is_whitespace) {
        return false;
    }
    let rest = rest.trim_start();
    let rest = match rest.strip_prefix('_') {
        Some(r) => r,
        None => return false,
    };
    // `_` must not be the start of a longer identifier (e.g. `_result`).
    if rest.starts_with(is_ident_char) {
        return false;
    }
    rest.trim_start().starts_with('=')
}

/// Extract the identifier bound by `let <ident> = ...` on this line, if any.
/// Returns None for `let _ = ...` and for non-`let` lines.
fn let_binding_ident(line: &str) -> Option<String> {
    let rest = line.trim_start().strip_prefix("let")?;
    if !rest.starts_with(char::is_whitespace) {
        return None;
    }
    let rest = rest.trim_start();
    // Optional `mut` (as a whole word).
    let rest = match rest.strip_prefix("mut") {
        Some(r) if r.starts_with(char::is_whitespace) => r.trim_start(),
        _ => rest,
    };
    let ident: String = rest.chars().take_while(|c| is_ident_char(*c)).collect();
    if ident.is_empty() || ident == "_" {
        return None;
    }
    Some(ident)
}

/// Search a window of following lines for a handling use of `ident`.
fn ident_checked_in_window(ident: &str, lines: &[&str], start: usize, window: usize) -> bool {
    if start >= lines.len() {
        return false;
    }
    let end = (start + window).min(lines.len());
    for raw in &lines[start..end] {
        let line = strip_line_comment(raw);
        let mut search_from = 0usize;
        while let Some(rel) = line.get(search_from..).and_then(|s| s.find(ident)) {
            let pos = search_from + rel;
            let after_idx = pos + ident.len();

            let before_ok = pos == 0
                || line[..pos]
                    .chars()
                    .next_back()
                    .map_or(true, |c| !is_ident_char(c));
            let after_ok = line[after_idx..]
                .chars()
                .next()
                .map_or(true, |c| !is_ident_char(c));

            if before_ok && after_ok {
                let rest = line[after_idx..].trim_start();
                let pre = line[..pos].trim_end();
                if rest.starts_with('?')
                    || rest.starts_with(".is_ok")
                    || rest.starts_with(".is_err")
                    || rest.starts_with(".map")
                    || rest.starts_with(".and_then")
                    || rest.starts_with(".unwrap")
                    || rest.starts_with(".expect")
                    || rest.starts_with(".ok")
                    || rest.starts_with(".err")
                    || pre.ends_with("match")
                    || pre.ends_with("return")
                    || (pre.ends_with('=')
                        && (line.contains("if let") || line.contains("while let")))
                {
                    return true;
                }
            }
            search_from = after_idx.max(pos + 1);
            if search_from >= line.len() {
                break;
            }
        }
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
            Chain::Ink,
            std::collections::HashMap::new(),
        );
        CrossContractDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_unchecked_invoke() {
        let source = r#"
            fn call_other(&mut self) {
                let _ = self.other_contract.try_invoke();
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect unchecked try_invoke");
    }

    #[test]
    fn test_no_finding_with_question_mark() {
        let source = r#"
            fn call_other(&mut self) -> Result<(), Error> {
                let result = self.other_contract.try_invoke()?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with ? operator");
    }

    // FP idx 0: `let _ = ...try_invoke()?;` -- Ok payload discarded but Err
    // still propagates via `?`. Must NOT flag.
    #[test]
    fn test_no_finding_let_underscore_question_mark() {
        let source = r#"
            fn ping(&mut self) -> Result<(), Error> {
                // Ok value intentionally ignored; Err still propagates to caller
                let _ = self.other_contract.try_invoke()?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "let _ = ...try_invoke()? propagates errors and must not flag"
        );
    }

    // FP idx 0 (bonus): `let _result = ...try_invoke()?;` must not be treated as
    // a discard by substring match on "let _".
    #[test]
    fn test_no_finding_let_underscore_prefixed_binding() {
        let source = r#"
            fn ping(&mut self) -> Result<(), Error> {
                let _result = self.other_contract.try_invoke()?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "let _result binding is not a discard and is handled by ?"
        );
    }

    // FP idx 1: comments, doc comments and string literals mentioning try_invoke.
    #[test]
    fn test_no_finding_comments_and_strings() {
        let source = r#"
            /// Calls the callee via try_invoke and surfaces LangError to the caller.
            fn docs_only(&self) {
                // NOTE: we deliberately avoid try_invoke here and use invoke() instead
                ink::env::debug_println!("skipping try_invoke path");
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "comments and string literals must not be flagged"
        );
    }

    // FP idx 2: result explicitly checked via .is_err().
    #[test]
    fn test_no_finding_is_err_check() {
        let source = r#"
            fn notify(&mut self) -> Result<(), Error> {
                if self.other_contract.try_invoke().is_err() {
                    return Err(Error::CalleeFailed);
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            ".is_err() check must not be flagged"
        );
    }

    // FP idx 3: result bound and matched a few lines later (blank line between).
    #[test]
    fn test_no_finding_match_after_blank_line() {
        let source = r#"
            fn forward(&mut self) -> Result<(), Error> {
                let outcome = self.other_contract.try_invoke();

                match outcome {
                    Ok(Ok(v)) => { self.total = v; Ok(()) }
                    _ => Err(Error::CalleeFailed),
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "binding matched later must not be flagged"
        );
    }

    // FP idx 4: try_invoke as tail expression delegating the Result to caller.
    #[test]
    fn test_no_finding_tail_expression() {
        let source = r#"
            fn call_callee(&mut self) -> Result<ink::MessageResult<u32>, ink::env::Error> {
                build_call::<DefaultEnvironment>()
                    .call(self.callee)
                    .returns::<u32>()
                    .try_invoke()
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "tail-expression delegation must not be flagged"
        );
    }

    // Sanity: a genuinely unchecked bound call whose binding is never used is
    // still flagged (idx 3 guard must not over-suppress).
    #[test]
    fn test_detects_unused_binding() {
        let source = r#"
            fn call_other(&mut self) {
                let outcome = self.other_contract.try_invoke();
                self.counter += 1;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "unchecked call with unused binding must still flag"
        );
    }
}
