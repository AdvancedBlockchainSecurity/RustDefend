use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, ExprCall, ExprMethodCall, ExprPath, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingRentExemptDetector;

impl Detector for MissingRentExemptDetector {
    fn id(&self) -> &'static str {
        "SOL-011"
    }
    fn name(&self) -> &'static str {
        "missing-rent-exempt"
    }
    fn description(&self) -> &'static str {
        "Detects create_account calls without rent-exemption checks"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();

        // Build a file-local view of every function so we can resolve whether a
        // rent-exemption computation lives one call away (in a callee helper) or
        // is threaded in from a caller. This is sound and file-local: we only
        // suppress when we can actually read the other function's body and see
        // the `minimum_balance` computation. Cross-file callers/callees are not
        // resolvable here (bodies aren't retained in the crate call graph), so
        // those cases remain flagged.
        let mut collector = FunctionCollector {
            functions: Vec::new(),
        };
        collector.visit_file(&ctx.ast);

        // name -> list of function/method names it calls
        let mut fn_calls: HashMap<String, Vec<String>> = HashMap::new();
        // name -> whether its body computes a rent-exempt minimum
        let mut fn_has_rent: HashMap<String, bool> = HashMap::new();

        for f in &collector.functions {
            let name = f.sig.ident.to_string();
            let calls = collect_call_names(f);
            let has_rent = body_computes_rent(&fn_body_source(f));

            fn_calls.entry(name.clone()).or_default().extend(calls);
            fn_has_rent
                .entry(name)
                .and_modify(|v| *v = *v || has_rent)
                .or_insert(has_rent);
        }

        let mut visitor = RentVisitor {
            findings: &mut findings,
            ctx,
            fn_calls: &fn_calls,
            fn_has_rent: &fn_has_rent,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// A rent-exempt minimum computation, precisely: `Rent::get()?.minimum_balance(..)`
/// (token stream, so `minimum_balance` is a single token) or the older
/// `Rent::minimum_balance(&rent, space)` form. We deliberately key on
/// `minimum_balance` rather than the broad "rent"/"Rent" substring the intra-body
/// heuristic uses, so cross-function suppression only fires on the real
/// computation and never on an incidental identifier.
fn body_computes_rent(body_src: &str) -> bool {
    body_src.contains("minimum_balance")
}

/// Collect the names of every function and method invoked in a function body.
/// For a call like `system_instruction::create_account(..)` this yields the last
/// path segment (`create_account`); for `x.minimum_balance(..)` it yields
/// `minimum_balance`.
fn collect_call_names(func: &ItemFn) -> Vec<String> {
    let mut c = CallNameCollector { names: Vec::new() };
    c.visit_item_fn(func);
    c.names
}

struct CallNameCollector {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for CallNameCollector {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let Expr::Path(ExprPath { path, .. }) = node.func.as_ref() {
            if let Some(seg) = path.segments.last() {
                self.names.push(seg.ident.to_string());
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        self.names.push(node.method.to_string());
        syn::visit::visit_expr_method_call(self, node);
    }
}

/// Detect an actual account-creation invocation in this function, rather than a
/// mere textual mention of `CreateAccount` (an enum variant / instruction name).
/// Real creation is one of:
///   * a call whose callee (or method) is `create_account` /
///     `create_account_with_seed`, or
///   * use of the `CreateAccount` CPI struct in an executing context
///     (`invoke` / `invoke_signed` / `CpiContext`).
fn creates_account(calls: &[String], body_src: &str) -> bool {
    let has_create_call = calls
        .iter()
        .any(|c| c == "create_account" || c == "create_account_with_seed");
    if has_create_call {
        return true;
    }

    let uses_create_account_struct = body_src.contains("CreateAccount");
    let has_exec_context = calls.iter().any(|c| c == "invoke" || c == "invoke_signed")
        || body_src.contains("CpiContext");

    uses_create_account_struct && has_exec_context
}

/// True for `#[cfg(test)]` exactly (not `cfg(feature = "...")`, etc.).
fn is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if attr.path().is_ident("cfg") {
            let toks: String = attr
                .meta
                .to_token_stream()
                .to_string()
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();
            return toks == "cfg(test)";
        }
        false
    })
}

/// True if the function carries a test attribute (`#[test]`, `#[tokio::test]`,
/// `#[ink::test]`, `#[async_std::test]`).
fn is_test_fn(attrs: &[Attribute]) -> bool {
    has_attribute(attrs, "test")
        || has_attribute(attrs, "tokio::test")
        || has_attribute(attrs, "ink::test")
        || has_attribute(attrs, "async_std::test")
}

struct RentVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    fn_calls: &'a HashMap<String, Vec<String>>,
    fn_has_rent: &'a HashMap<String, bool>,
}

impl<'a> RentVisitor<'a> {
    /// A callee of `fn_name` (resolvable in this file) computes the rent-exempt
    /// minimum — e.g. `let lamports = required_lamports(space)?;`.
    fn callee_computes_rent(&self, calls: &[String]) -> bool {
        calls
            .iter()
            .any(|c| self.fn_has_rent.get(c) == Some(&true))
    }

    /// A caller of `fn_name` (resolvable in this file) computes the rent-exempt
    /// minimum and threads it in — the canonical `create_pda_account` helper
    /// shape where the caller does `Rent::get()?.minimum_balance(space)`.
    fn caller_computes_rent(&self, fn_name: &str) -> bool {
        self.fn_calls.iter().any(|(caller, callees)| {
            caller != fn_name
                && callees.iter().any(|c| c == fn_name)
                && self.fn_has_rent.get(caller) == Some(&true)
        })
    }
}

impl<'ast, 'a> Visit<'ast> for RentVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Never descend into #[cfg(test)] modules — their contents are compiled
        // out of any deployed program and carry no exploitable surface.
        if is_cfg_test(&node.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();
        if fn_name.starts_with("test_") || fn_name.contains("_test") {
            return;
        }

        // Skip test functions regardless of their name.
        if is_test_fn(&func.attrs) {
            syn::visit::visit_item_fn(self, func);
            return;
        }

        let body_src = fn_body_source(func);
        let calls = collect_call_names(func);

        // Require an actual account-creation invocation, not just a textual
        // mention of `CreateAccount` (enum variant / dispatcher match arm).
        if !creates_account(&calls, &body_src) {
            syn::visit::visit_item_fn(self, func);
            return;
        }

        // Intra-body rent-exemption evidence (original heuristic).
        let has_rent_check = body_src.contains("Rent")
            || body_src.contains("rent")
            || body_src.contains("minimum_balance")
            || body_src.contains("exempt");

        // Anchor's `init` constraint handles rent automatically.
        if has_rent_check || body_src.contains("init") {
            syn::visit::visit_item_fn(self, func);
            return;
        }

        // Cross-function (file-local, resolved) rent-exemption evidence: the
        // computation lives in a callee helper, or is threaded in from a caller.
        if self.callee_computes_rent(&calls) || self.caller_computes_rent(&fn_name) {
            syn::visit::visit_item_fn(self, func);
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-011".to_string(),
            name: "missing-rent-exempt".to_string(),
            severity: Severity::Medium,
            confidence: Confidence::Medium,
            message: format!(
                "Function '{}' creates account without rent-exemption check",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation:
                "Use Rent::get()?.minimum_balance(space) to ensure accounts are rent-exempt"
                    .to_string(),
            chain: Chain::Solana,
        });

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
            Chain::Solana,
            std::collections::HashMap::new(),
        );
        MissingRentExemptDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_rent_check() {
        let source = r#"
            fn initialize(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
                let ix = system_instruction::create_account(
                    payer.key, new_account.key, lamports, space as u64, program_id,
                );
                invoke(&ix, &[payer.clone(), new_account.clone()])?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing rent check");
    }

    #[test]
    fn test_no_finding_with_rent_check() {
        let source = r#"
            fn initialize(program_id: &Pubkey, accounts: &[AccountInfo]) -> ProgramResult {
                let rent = Rent::get()?;
                let lamports = rent.minimum_balance(space);
                let ix = system_instruction::create_account(
                    payer.key, new_account.key, lamports, space as u64, program_id,
                );
                invoke(&ix, &[payer.clone(), new_account.clone()])?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with rent check");
    }

    // FP idx 1: instruction dispatcher that only names a `CreateAccount` enum
    // variant and delegates — it creates nothing itself.
    #[test]
    fn test_no_finding_dispatcher_only_names_variant() {
        let source = r#"
            fn process_instruction(
                program_id: &Pubkey,
                accounts: &[AccountInfo],
                data: &[u8],
            ) -> ProgramResult {
                match MyInstruction::unpack(data)? {
                    MyInstruction::CreateAccount { space } => process_create(program_id, accounts, space),
                    MyInstruction::Transfer { amount } => process_transfer(accounts, amount),
                    MyInstruction::Close => process_close(accounts),
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Dispatcher that only names a CreateAccount variant must not be flagged"
        );
    }

    // FP idx 2: rent-exempt minimum computed in a locally-defined callee helper
    // whose name contains no rent keyword.
    #[test]
    fn test_no_finding_callee_computes_rent() {
        let source = r#"
            fn allocate_vault(payer: &AccountInfo, vault: &AccountInfo, space: u64) -> ProgramResult {
                let lamports = required_lamports(space)?;
                let ix = system_instruction::create_account(
                    payer.key, vault.key, lamports, space, &crate::ID,
                );
                invoke(&ix, &[payer.clone(), vault.clone()])
            }

            fn required_lamports(space: usize) -> Result<u64, ProgramError> {
                Ok(Rent::get()?.minimum_balance(space))
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Caller whose callee computes minimum_balance must not be flagged"
        );
    }

    // FP idx 0: canonical PDA-creation helper that receives the pre-computed
    // rent-exempt lamports as a parameter; the caller computes it.
    #[test]
    fn test_no_finding_caller_computes_rent() {
        let source = r#"
            fn create_pda_account(
                payer: &AccountInfo,
                new_account: &AccountInfo,
                lamports: u64,
                space: u64,
                owner: &Pubkey,
            ) -> ProgramResult {
                let ix = system_instruction::create_account(
                    payer.key, new_account.key, lamports, space, owner,
                );
                invoke_signed(&ix, &[payer.clone(), new_account.clone()], &[])
            }

            fn open_vault(payer: &AccountInfo, new_account: &AccountInfo, space: u64) -> ProgramResult {
                let lamports = Rent::get()?.minimum_balance(space as usize);
                create_pda_account(payer, new_account, lamports, space, &crate::ID)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Helper whose caller threads in minimum_balance must not be flagged"
        );
    }

    // FP idx 3: account creation inside a #[cfg(test)] module / #[test] fn whose
    // name does not match the legacy skip-list.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                use super::*;

                #[test]
                fn creates_vault_account() {
                    let ix = system_instruction::create_account(
                        &payer.pubkey(), &vault.pubkey(), 1_000_000, 8, &id(),
                    );
                    let result = banks_client_process(ix);
                    assert!(result.is_ok());
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Account creation in a #[cfg(test)] module must not be flagged"
        );
    }

    // Soundness guard: when NO rent computation exists anywhere in the resolvable
    // call chain (caller passes a hardcoded value), the real vulnerability must
    // still fire.
    #[test]
    fn test_still_fires_when_no_rent_anywhere() {
        let source = r#"
            fn create_pda_account(
                payer: &AccountInfo,
                new_account: &AccountInfo,
                lamports: u64,
                space: u64,
                owner: &Pubkey,
            ) -> ProgramResult {
                let ix = system_instruction::create_account(
                    payer.key, new_account.key, lamports, space, owner,
                );
                invoke_signed(&ix, &[payer.clone(), new_account.clone()], &[])
            }

            fn open_vault(payer: &AccountInfo, new_account: &AccountInfo, space: u64) -> ProgramResult {
                let lamports = 1_000_000u64;
                create_pda_account(payer, new_account, lamports, space, &crate::ID)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Underfunded create with no rent computation must still fire"
        );
    }
}
