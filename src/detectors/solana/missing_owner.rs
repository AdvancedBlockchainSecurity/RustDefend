use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Block, ExprCall, ExprMethodCall, ItemFn, ItemMod};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;
use crate::utils::call_graph::{self, CheckKind};

pub struct MissingOwnerDetector;

impl Detector for MissingOwnerDetector {
    fn id(&self) -> &'static str {
        "SOL-002"
    }
    fn name(&self) -> &'static str {
        "missing-owner-check"
    }
    fn description(&self) -> &'static str {
        "Detects deserialization of account data without verifying account owner"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Require Solana-specific source markers to avoid cross-chain FPs
        if !ctx.source.contains("solana_program")
            && !ctx.source.contains("anchor_lang")
            && !ctx.source.contains("AccountInfo")
            && !ctx.source.contains("ProgramResult")
            && !ctx.source.contains("solana_sdk")
        {
            return Vec::new();
        }

        // Skip framework/library source files
        let file_str = ctx.file_path.to_string_lossy();
        if file_str.contains("/anchor-spl/")
            || file_str.contains("/anchor_spl/")
            || file_str.contains("/anchor-lang/")
            || file_str.contains("/anchor_lang/")
            || file_str.contains("/codegen/")
            || file_str.contains("/interface/src/")
            || file_str.contains("/spl-token/")
            || file_str.contains("/spl_token/")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = OwnerVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Deserialization primitives that decode raw bytes into typed state.
const DESER_PATTERNS: [&str; 5] = [
    "deserialize",
    "try_from_slice",
    "unpack",
    "try_deserialize",
    "try_borrow_data",
];

/// True if the attribute list marks this as a unit/integration test function.
///
/// Test code (`#[test]`, `#[tokio::test]`, `#[ink::test]`, ...) decodes fixture
/// bytes, never untrusted on-chain account data, so an owner check is meaningless
/// and any finding there is a false positive.
fn is_test_fn(attrs: &[Attribute]) -> bool {
    has_attribute(attrs, "test")
        || has_attribute(attrs, "tokio::test")
        || has_attribute(attrs, "async_std::test")
        || has_attribute(attrs, "ink::test")
}

/// Structurally detect whether the block contains a real deserialization *call*
/// (an `ExprCall` whose final path segment, or an `ExprMethodCall` whose method
/// name, matches a deserialization primitive).
///
/// Unlike a body-wide substring scan, this ignores tokens that appear only inside
/// string literals / `msg!(...)` text or comments, eliminating those false
/// positives while still catching every genuine `X::try_from_slice(..)` /
/// `.unpack(..)` invocation.
fn has_deser_call(block: &Block) -> bool {
    struct DeserFinder {
        found: bool,
    }
    impl<'ast> Visit<'ast> for DeserFinder {
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            let name = node.method.to_string();
            if DESER_PATTERNS.iter().any(|p| name.contains(p)) {
                self.found = true;
            }
            syn::visit::visit_expr_method_call(self, node);
        }
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let syn::Expr::Path(p) = node.func.as_ref() {
                if let Some(seg) = p.path.segments.last() {
                    let name = seg.ident.to_string();
                    if DESER_PATTERNS.iter().any(|pat| name.contains(pat)) {
                        self.found = true;
                    }
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }
    let mut finder = DeserFinder { found: false };
    finder.visit_block(block);
    finder.found
}

/// True if the token-stream text of a function body actually reads account data.
///
/// Deserializing *account* data always routes through the `AccountInfo` data
/// buffer, which tokenizes as `account . data` (`. data`) or goes through a
/// `borrow` / `try_borrow_data` call. Instruction payloads (`instruction_data`,
/// `input`, ...) are single identifiers and match neither, so a body that
/// deserializes only instruction bytes is correctly treated as having nothing an
/// owner check could protect.
fn reads_account_data(body_src: &str) -> bool {
    body_src.contains("borrow") || body_src.contains(". data")
}

/// True if the body text contains an actual account-owner verification.
///
/// Recognizes:
///  - the original `owner` + `program_id`/`key()` idiom,
///  - comparison against a program-id constant (`spl_token::id()`, `crate::ID`,
///    `check_id`),
///  - any direct `.owner ==` / `.owner !=` comparison regardless of the RHS.
fn body_has_owner_check(body_src: &str) -> bool {
    let mentions_owner = body_src.contains("owner");
    (mentions_owner
        && (body_src.contains("program_id")
            || body_src.contains("key ()")
            || body_src.contains(":: id ()")
            || body_src.contains(":: ID")
            || body_src.contains("check_id")))
        || body_src.contains("owner ==")
        || body_src.contains("owner !=")
}

struct OwnerVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'a> OwnerVisitor<'a> {
    /// Resolve the direct callees of `fn_name` in this file's AST and return true
    /// if any of them actually performs an owner check in its own body.
    ///
    /// This is sound callee-propagation: rather than a name-based skip, it looks
    /// up the concrete callee `ItemFn` and confirms the owner-comparison tokens
    /// are really present (the Metaplex `assert_owned_by(account, pid)?` idiom).
    fn callee_has_owner_check(&self, fn_name: &str) -> bool {
        let callees = match self.ctx.call_graph.get(fn_name) {
            Some(info) => &info.calls,
            None => return false,
        };
        if callees.is_empty() {
            return false;
        }
        for item in &self.ctx.ast.items {
            if let syn::Item::Fn(f) = item {
                let name = f.sig.ident.to_string();
                if name != fn_name && callees.iter().any(|c| c == &name) {
                    let body = fn_body_source(f);
                    if body_has_owner_check(&body) {
                        return true;
                    }
                }
            }
        }
        false
    }
}

impl<'ast, 'a> Visit<'ast> for OwnerVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Do not descend into `#[cfg(test)]` modules: test code deserializes
        // fixture bytes, not untrusted account data.
        if has_attribute_with_value(&node.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test functions (#[test] / #[tokio::test] / #[ink::test] / ...).
        if is_test_fn(&func.attrs) {
            return;
        }

        let fn_src = func.to_token_stream().to_string();

        // Skip Anchor patterns (Account<'info, T> handles this automatically)
        if fn_src.contains("Account <") || fn_src.contains("Account<") {
            if !fn_src.contains("AccountInfo") {
                return;
            }
        }

        // Look for a *real* deserialization call (AST-level; ignores string
        // literals / comments so `msg!("...unpack...")` no longer matches).
        if !has_deser_call(&func.block) {
            return;
        }

        let body_src = fn_body_source(func);

        // Only account-data deserialization is in scope. If the function decodes
        // only instruction bytes (e.g. the canonical `try_from_slice(instruction_data)`
        // entrypoint) it never touches `AccountInfo` data and there is nothing an
        // owner check could protect.
        if !reads_account_data(&body_src) {
            return;
        }

        // Check for owner verification in this function's own body.
        if body_has_owner_check(&body_src) {
            return;
        }

        let fn_name = func.sig.ident.to_string();

        // A caller in the (cross-)call graph already checks owner.
        if call_graph::caller_has_check(&self.ctx.call_graph, &fn_name, CheckKind::OwnerCheck) {
            return;
        }

        // The owner check is delegated to a resolved callee helper.
        if self.callee_has_owner_check(&fn_name) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-002".to_string(),
            name: "missing-owner-check".to_string(),
            severity: Severity::Critical,
            confidence: Confidence::High,
            message: format!(
                "Function '{}' deserializes account data without verifying account owner",
                func.sig.ident
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add `if account.owner != program_id { return Err(...) }` before deserialization, or use Anchor's `Account<'info, T>`".to_string(),
            chain: Chain::Solana,
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_detector(source: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let graph = crate::utils::call_graph::build_call_graph(&ast);
        let ctx = ScanContext::new(
            std::path::PathBuf::from("test.rs"),
            source.to_string(),
            ast,
            Chain::Solana,
            graph,
        );
        MissingOwnerDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_owner_check() {
        let source = r#"
            fn process(account: &AccountInfo) {
                let data = MyData::deserialize(&mut &account.data.borrow()[..]).unwrap();
                data.amount += 100;
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing owner check");
    }

    #[test]
    fn test_no_finding_caller_checks_owner() {
        let source = r#"
            fn process(account: &AccountInfo, program_id: &Pubkey) {
                if account.owner != program_id {
                    return Err(ProgramError::IncorrectProgramId);
                }
                helper(account);
            }

            fn helper(account: &AccountInfo) {
                let data = MyData::deserialize(&mut &account.data.borrow()[..]).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when caller checks owner (call graph analysis)"
        );
    }

    #[test]
    fn test_no_finding_with_owner_check() {
        let source = r#"
            fn process(account: &AccountInfo, program_id: &Pubkey) {
                if account.owner != program_id {
                    return Err(ProgramError::IncorrectProgramId);
                }
                let data = MyData::deserialize(&mut &account.data.borrow()[..]).unwrap();
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with owner check");
    }

    // --- False-positive regression tests ---------------------------------

    // FP idx 0: canonical entrypoint deserializing instruction_data (not account data).
    #[test]
    fn test_no_finding_instruction_data_entrypoint() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            pub fn process_instruction(
                program_id: &Pubkey,
                accounts: &[AccountInfo],
                instruction_data: &[u8],
            ) -> ProgramResult {
                let instruction = MyInstruction::try_from_slice(instruction_data)
                    .map_err(|_| ProgramError::InvalidInstructionData)?;
                match instruction {
                    MyInstruction::Init => msg!("init"),
                }
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag deserialization of instruction_data (no account data read)"
        );
    }

    // FP idx 1: owner verified against a program-ID constant (spl_token::id()).
    #[test]
    fn test_no_finding_owner_checked_against_constant() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            pub fn read_token_account(token_account: &AccountInfo) -> ProgramResult {
                if token_account.owner != &spl_token::id() {
                    return Err(ProgramError::IncorrectProgramId);
                }
                let state = spl_token::state::Account::unpack(&token_account.data.borrow())?;
                msg!("amount {}", state.amount);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when .owner is compared against spl_token::id()"
        );
    }

    // FP idx 2: owner check delegated to a resolved callee helper.
    #[test]
    fn test_no_finding_owner_check_in_callee() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            fn assert_owned_by(account: &AccountInfo, expected: &Pubkey) -> ProgramResult {
                if account.owner != expected {
                    return Err(ProgramError::IllegalOwner);
                }
                Ok(())
            }

            pub fn process(account: &AccountInfo, pid: &Pubkey) -> ProgramResult {
                assert_owned_by(account, pid)?;
                let data = MyState::try_from_slice(&account.data.borrow())?;
                msg!("{}", data.value);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when owner check is delegated to a resolved helper"
        );
    }

    // FP idx 3: findings emitted on #[cfg(test)] / #[test] code.
    #[test]
    fn test_no_finding_in_cfg_test_module() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            #[cfg(test)]
            mod tests {
                #[test]
                fn test_state_roundtrip() {
                    let bytes = vec![0u8; 32];
                    let state = MyState::try_from_slice(&bytes).unwrap();
                    assert_eq!(state.value, 0);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag deserialization inside #[cfg(test)] code"
        );
    }

    // FP idx 4: deser pattern matched only inside a string literal (msg! text).
    #[test]
    fn test_no_finding_deser_word_in_string_literal() {
        let source = r#"
            use solana_program::account_info::AccountInfo;

            pub fn log_failure(account: &AccountInfo) -> ProgramResult {
                msg!("failed to unpack account data for {}", account.key);
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when 'unpack' appears only in a string literal"
        );
    }
}
