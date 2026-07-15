use quote::ToTokens;
use syn::visit::Visit;
use syn::{ItemFn, ItemMod, Local, Pat, Stmt};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct CpiReentrancyDetector;

impl Detector for CpiReentrancyDetector {
    fn id(&self) -> &'static str {
        "SOL-009"
    }
    fn name(&self) -> &'static str {
        "cpi-reentrancy"
    }
    fn description(&self) -> &'static str {
        "Detects state mutations after CPI calls (CEI violation) - mitigated by Solana's account locking"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::Low
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = ReentrancyVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct ReentrancyVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for ReentrancyVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Never scan `#[cfg(test)]` modules — their mutations are test fixtures,
        // not on-chain state, and produce noise.
        if attrs_are_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (#[test], #[tokio::test], #[ink::test], ...).
        if attrs_are_test(&func.attrs) {
            return;
        }

        let stmts = &func.block.stmts;
        let mut seen_cpi = false;
        let mut cpi_line = 0usize;
        // Variables bound to a `CpiContext::new(..)` construction. The CPI does
        // not actually happen until such a context is *consumed* by a wrapper
        // call (e.g. `token::transfer(cpi_ctx, ..)`), so construction alone must
        // not arm the detector.
        let mut pending_ctx_vars: Vec<String> = Vec::new();

        for stmt in stmts {
            // Work over the statement's token stream with string-literal
            // contents removed, so matches never fire on the text inside a
            // `msg!("data = {}")` log or any other string literal.
            let clean = cleaned_stmt_string(stmt);
            let stmt_line = get_stmt_line(stmt);

            // (1) `let cpi_ctx = CpiContext::new(..)` merely builds an in-memory
            // struct. Record the binding but do NOT treat it as the CPI.
            if let Stmt::Local(local) = stmt {
                if clean.contains("CpiContext") && clean.contains("new") {
                    if let Some(id) = local_binding_ident(local) {
                        pending_ctx_vars.push(id);
                    }
                    continue;
                }
            }

            // (2) Does this statement perform an actual cross-program invocation?
            let native = clean.contains("invoke (")
                || clean.contains("invoke(")
                || clean.contains("invoke_signed");
            // Anchor-style CPI: the wrapper call that consumes a CpiContext
            // (`::cpi::`, an inline `CpiContext::..` inside a call, or a call
            // that passes a previously-built ctx variable).
            let anchor_cpi = clean.contains(":: cpi ::")
                || clean.contains("CpiContext")
                || pending_ctx_vars.iter().any(|v| uses_var_in_call(&clean, v));

            if native || anchor_cpi {
                seen_cpi = true;
                cpi_line = stmt_line;
                // The CPI statement itself is never the "mutation after CPI".
                continue;
            }

            // (3) After a CPI, look for a *write* to persistent account state.
            if seen_cpi && stmt_line > cpi_line {
                if is_state_mutation(stmt, &clean) {
                    self.findings.push(Finding {
                        detector_id: "SOL-009".to_string(),
                        name: "cpi-reentrancy".to_string(),
                        severity: Severity::Medium,
                        confidence: Confidence::Low,
                        message: format!(
                            "Function '{}' mutates state after CPI call (CEI violation)",
                            func.sig.ident
                        ),
                        file: self.ctx.file_path.clone(),
                        line: stmt_line,
                        column: 1,
                        snippet: snippet_at_line(&self.ctx.source, stmt_line),
                        recommendation: "Solana's account locking mitigates CPI reentrancy, but CEI violations should be avoided for defense-in-depth. Move state mutations before CPI calls".to_string(),
                        chain: Chain::Solana,
                    });
                }
            }
        }
    }
}

/// Decide whether a statement (after a CPI) actually *writes* persistent
/// account state. Reads (`try_borrow_data`, `deserialize`, comparisons) and
/// mutations of purely local values (a stack `RefCell`) are not violations.
fn is_state_mutation(stmt: &Stmt, clean: &str) -> bool {
    // --- serialization write ---
    // `serialize` / `try_serialize` write bytes back into an account. Exclude
    // `deserialize` / `try_from_slice`, which only *decode* bytes (the original
    // `contains("serialize")` substring-matched "deserialize").
    let is_serialize_write = clean.contains("serialize")
        && !clean.contains("deserialize")
        && !clean.contains("try_from_slice");

    // --- mutable borrow of account data / lamports ---
    // Restrict to account-data forms; a bare `borrow_mut` on a local RefCell is
    // not persistent state.
    let is_account_borrow_mut = clean.contains("try_borrow_mut_data")
        || clean.contains("try_borrow_mut_lamports")
        || clean.contains("borrow_mut_data")
        || clean.contains("borrow_mut_lamports")
        || (clean.contains(". data") && clean.contains("borrow_mut"))
        || (clean.contains("lamports") && clean.contains("borrow_mut"));

    // --- direct assignment into account data ---
    // Only expression statements (e.g. `data[0] = 1;`) count. `let data = ..`
    // bindings are reads of data into a fresh local, not writes, and are
    // excluded. Require a real assignment operator (not `==`/`>=`/`<=`/`!=`).
    let is_data_assign =
        !matches!(stmt, Stmt::Local(_)) && clean.contains("data") && has_assignment_op(clean);

    is_serialize_write || is_account_borrow_mut || is_data_assign
}

/// True if the cleaned statement text contains a real assignment operator.
/// Deliberately excludes comparisons: in a token-stream string, `==`, `>=`,
/// `<=`, `!=` never render the standalone " = " sequence.
fn has_assignment_op(clean: &str) -> bool {
    if clean.contains(" = ") {
        return true;
    }
    const COMPOUND: [&str; 10] = [
        " += ", " -= ", " *= ", " /= ", " %= ", " &= ", " |= ", " ^= ", " <<= ", " >>= ",
    ];
    COMPOUND.iter().any(|op| clean.contains(op))
}

/// Render a statement's token stream with the *contents* of string/byte-string
/// literals stripped out, so substring heuristics never match text that lives
/// inside a string literal (e.g. a `msg!` log message).
fn cleaned_stmt_string(stmt: &Stmt) -> String {
    let ts = stmt.to_token_stream();
    let mut s = ts.to_string();
    let mut lits = Vec::new();
    collect_string_literals(ts, &mut lits);
    for lit in lits {
        s = s.replace(&lit, " __STRLIT__ ");
    }
    s
}

fn collect_string_literals(ts: proc_macro2::TokenStream, out: &mut Vec<String>) {
    for tt in ts {
        match tt {
            proc_macro2::TokenTree::Literal(lit) => {
                let repr = lit.to_string();
                // String / byte-string / raw-string literals all contain a `"`;
                // numeric and (ordinary) char literals do not.
                if repr.contains('"') {
                    out.push(repr);
                }
            }
            proc_macro2::TokenTree::Group(g) => collect_string_literals(g.stream(), out),
            _ => {}
        }
    }
}

/// Extract the identifier bound by a `let` pattern (`let x = ..`, `let mut x`,
/// `let x: T = ..`). Returns None for tuple/struct/other patterns.
fn local_binding_ident(local: &Local) -> Option<String> {
    fn from_pat(pat: &Pat) -> Option<String> {
        match pat {
            Pat::Ident(pi) => Some(pi.ident.to_string()),
            Pat::Type(pt) => from_pat(&pt.pat),
            _ => None,
        }
    }
    from_pat(&local.pat)
}

/// True if `var` appears as a standalone identifier inside a call in `clean`.
/// Token-boundary aware so `ctx` does not match `context`.
fn uses_var_in_call(clean: &str, var: &str) -> bool {
    if !clean.contains('(') {
        return false;
    }
    clean
        .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        .any(|tok| tok == var)
}

/// True if the attribute list marks a test item: `#[cfg(test)]`, `#[test]`,
/// `#[tokio::test]`, `#[ink::test]`, `#[async_std::test]`, etc.
fn attrs_are_test(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|a| {
        let path = a.path();
        if path.is_ident("cfg") {
            let toks = a.meta.to_token_stream().to_string();
            if toks.contains("test") {
                return true;
            }
        }
        let joined = path
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect::<Vec<_>>()
            .join("::");
        joined == "test" || joined.ends_with("::test")
    })
}

fn get_stmt_line(stmt: &Stmt) -> usize {
    match stmt {
        Stmt::Local(local) => span_to_line(&local.let_token.span),
        Stmt::Expr(expr, _) => {
            // Best effort line extraction
            let tokens = expr.to_token_stream();
            let span = tokens
                .into_iter()
                .next()
                .map(|t| t.span())
                .unwrap_or_else(proc_macro2::Span::call_site);
            span_to_line(&span)
        }
        Stmt::Item(_) => 0,
        Stmt::Macro(m) => span_to_line(&m.mac.path.span()),
    }
}

use proc_macro2::Span;

trait PathSpan {
    fn span(&self) -> Span;
}

impl PathSpan for syn::Path {
    fn span(&self) -> Span {
        self.segments
            .first()
            .map(|s| s.ident.span())
            .unwrap_or_else(Span::call_site)
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
        CpiReentrancyDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_state_after_cpi() {
        let source = r#"
            fn process(accounts: &[AccountInfo]) -> ProgramResult {
                invoke(&ix, &accounts)?;
                let mut data = account.try_borrow_mut_data()?;
                data[0] = 1;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect state mutation after CPI"
        );
    }

    #[test]
    fn test_no_finding_state_before_cpi() {
        let source = r#"
            fn process(accounts: &[AccountInfo]) -> ProgramResult {
                let mut data = account.try_borrow_mut_data()?;
                data[0] = 1;
                invoke(&ix, &accounts)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag state mutation before CPI"
        );
    }

    // --- must still fire: serialization write after a real CPI ---
    #[test]
    fn test_detects_serialize_after_cpi() {
        let source = r#"
            fn process(accounts: &[AccountInfo]) -> ProgramResult {
                invoke(&ix, &accounts)?;
                state.serialize(&mut &mut account.data.borrow_mut()[..])?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect serialize write after CPI"
        );
    }

    // --- must still fire: mutation after an Anchor CPI wrapper call ---
    #[test]
    fn test_detects_mutation_after_anchor_cpi() {
        let source = r#"
            fn withdraw(ctx: Context<Withdraw>, amount: u64) -> Result<()> {
                let cpi_ctx = CpiContext::new(token_program, transfer_accounts);
                token::transfer(cpi_ctx, amount)?;
                let mut data = vault_info.try_borrow_mut_data()?;
                data[0] = 9;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect mutation after the CpiContext is consumed by transfer"
        );
    }

    // --- FP idx 0: read-only verification of CPI results ---
    #[test]
    fn test_no_finding_read_only_after_cpi() {
        let source = r#"
            fn read_only_after_cpi(accounts: &[AccountInfo]) -> ProgramResult {
                invoke(&ix, accounts)?;
                let data = account.try_borrow_data()?;
                if data[0] == 0 {
                    return Err(ProgramError::InvalidAccountData);
                }
                let state = TokenAccount::deserialize(&mut &vault.data.borrow()[..])?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Reads/deserialize/comparisons after CPI are not CEI violations"
        );
    }

    // --- FP idx 1: CpiContext construction is not the CPI ---
    #[test]
    fn test_no_finding_effects_before_real_cpi() {
        let source = r#"
            fn cei_compliant_withdraw(ctx: Context<Withdraw>, amount: u64) -> Result<()> {
                let cpi_ctx = CpiContext::new(token_program, transfer_accounts);
                let mut data = vault_info.try_borrow_mut_data()?;
                data[0] = 0;
                drop(data);
                token::transfer(cpi_ctx, amount)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Mutations before the CpiContext is consumed follow CEI and must not be flagged"
        );
    }

    // --- FP idx 2: borrow_mut on a local RefCell ---
    #[test]
    fn test_no_finding_local_refcell_borrow_mut() {
        let source = r#"
            fn local_state_after_cpi(accounts: &[AccountInfo]) -> ProgramResult {
                let counter = std::cell::RefCell::new(0u8);
                invoke(&ix, accounts)?;
                *counter.borrow_mut() += 1;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Mutating a stack-local RefCell is not a persistent-state CEI violation"
        );
    }

    // --- FP idx 3: msg! log line mentioning "data" and '=' ---
    #[test]
    fn test_no_finding_msg_log_after_cpi() {
        let source = r#"
            fn log_after_cpi(accounts: &[AccountInfo]) -> ProgramResult {
                invoke(&ix, accounts)?;
                msg!("data transferred = {}", amount);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A log message whose string mentions data/'=' must not be flagged"
        );
    }
}
