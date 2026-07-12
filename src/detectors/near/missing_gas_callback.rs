use quote::ToTokens;
use syn::visit::Visit;
use syn::ItemFn;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingGasCallbackDetector;

impl Detector for MissingGasCallbackDetector {
    fn id(&self) -> &'static str {
        "NEAR-012"
    }
    fn name(&self) -> &'static str {
        "missing-gas-for-callbacks"
    }
    fn description(&self) -> &'static str {
        "Detects cross-contract calls without explicit gas specification"
    }
    fn severity(&self) -> Severity {
        Severity::Medium
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Near
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Require NEAR-specific source markers to avoid cross-chain FPs
        if !ctx.source.contains("near_sdk")
            && !ctx.source.contains("near_contract_standards")
            && !ctx.source.contains("#[near_bindgen]")
            && !ctx.source.contains("#[near(")
            && !ctx.source.contains("env::predecessor_account_id")
            && !ctx.source.contains("env::signer_account_id")
            && !ctx.source.contains("Promise::new")
        {
            return Vec::new();
        }

        let mut findings = Vec::new();
        let mut visitor = GasVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

// Patterns that indicate an explicit gas specification. `fn_body_source` renders
// the body as a proc-macro2 token stream, which is space-separated (e.g.
// `. with_static_gas (`), so both spaced and legacy unspaced variants are listed.
const GAS_PATTERNS: &[&str] = &[
    "gas (",
    "Gas (",
    "gas(",
    "Gas(",
    ".with_static_gas(",
    "with_static_gas (",
    ".with_attached_gas(",
    "with_attached_gas (",
    ".with_unused_gas_weight(",
    // Token-stream (spaced) form of the gas-weight builder. The unspaced entry
    // above can never match real code because the body is a token stream, and
    // unlike `with_static_gas`/`with_attached_gas` it is not rescued by the
    // "gas (" substring ('gas' is followed by '_weight', not '(').
    "with_unused_gas_weight (",
    "GAS_FOR_",
    "CALLBACK_GAS",
    "TGAS",
    "TGas",
    "NearGas",
    "prepaid_gas",
];

struct GasVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

/// True if the function signature declares a parameter whose type mentions `Gas`
/// (e.g. `gas: Gas`, `gas_for_call: Gas`, `g: NearGas`). A typed gas parameter is
/// an explicit, caller-supplied gas budget passed into the cross-contract call.
fn has_typed_gas_param(func: &ItemFn) -> bool {
    func.sig.inputs.iter().any(|arg| {
        if let syn::FnArg::Typed(pat_type) = arg {
            pat_type.ty.to_token_stream().to_string().contains("Gas")
        } else {
            false
        }
    })
}

/// True if the token identifier is a SCREAMING_SNAKE_CASE constant containing the
/// substring `GAS` (e.g. `FT_TRANSFER_GAS`, `GAS_FOR_CALLBACK`, `DEFAULT_GAS`,
/// `BASE_GAS`). Mirrors the regex `\b[A-Z][A-Z0-9_]*GAS[A-Z0-9_]*\b`.
fn is_screaming_gas_ident(tok: &str) -> bool {
    // Must start with an uppercase ASCII letter.
    if !tok.chars().next().is_some_and(|c| c.is_ascii_uppercase()) {
        return false;
    }
    // Must be all-uppercase (SCREAMING_SNAKE): no lowercase letters allowed.
    if tok.chars().any(|c| c.is_ascii_lowercase()) {
        return false;
    }
    tok.contains("GAS")
}

/// True if `body_src` (a token-stream rendering) references any named gas constant
/// of the SCREAMING_SNAKE form (see `is_screaming_gas_ident`). Passing such a
/// constant as the gas argument is an explicit gas specification even when its
/// name is not on the hard-coded allow-list.
fn has_named_gas_constant(body_src: &str) -> bool {
    let bytes = body_src.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            if is_screaming_gas_ident(&body_src[start..i]) {
                return true;
            }
        } else {
            i += 1;
        }
    }
    false
}

impl<'ast, 'a> Visit<'ast> for GasVisitor<'a> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions
        if fn_name.starts_with("test_")
            || fn_name.ends_with("_test")
            || has_attribute(&func.attrs, "test")
        {
            return;
        }

        // Skip callback functions (they receive gas, don't specify it)
        if fn_name.starts_with("on_") || fn_name.ends_with("_callback") {
            return;
        }

        let body_src = fn_body_source(func);

        // `fn_body_source` is a token stream, so real code renders spaced
        // (e.g. `Promise :: new`, `. function_call (`). Only the spaced variants
        // are matched here; the previously-listed unspaced forms could only ever
        // match inside string literals (e.g. env::log_str("Promise::new ...")).
        let has_ext_call = body_src.contains("ext_self ::") || body_src.contains("ext_contract ::");
        let has_function_call = body_src.contains("function_call (");

        // Gas specification only matters for function-call actions and their
        // callbacks. A bare `Promise::new(x)` composed solely of batch actions
        // (transfer / create_account / deploy_contract / add_*_key / delete_account
        // / stake) takes no gas argument at all — its gas cost is fixed by the
        // protocol — so it is not a gas-requiring cross-contract call.
        let has_cross_contract = has_function_call || has_ext_call;
        if !has_cross_contract {
            return;
        }

        let has_gas_spec = GAS_PATTERNS.iter().any(|p| body_src.contains(p))
            || has_named_gas_constant(&body_src)
            || has_typed_gas_param(func);

        if !has_gas_spec {
            let line = span_to_line(&func.sig.ident.span());
            self.findings.push(Finding {
                detector_id: "NEAR-012".to_string(),
                name: "missing-gas-for-callbacks".to_string(),
                severity: Severity::Medium,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' makes cross-contract calls without explicit gas specification",
                    fn_name
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Specify gas explicitly with .with_static_gas() or Gas() to prevent callbacks from running out of gas".to_string(),
                chain: Chain::Near,
            });
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
            Chain::Near,
            std::collections::HashMap::new(),
        );
        MissingGasCallbackDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_gas() {
        // The function_call passes a literal `0` as gas (no explicit gas budget)
        // and the ext_self:: callback specifies no gas at all — a genuine
        // missing-gas cross-contract call.
        let source = r#"
            fn transfer_and_call(&mut self, receiver_id: AccountId, amount: U128) {
                self.internal_transfer(&env::predecessor_account_id(), &receiver_id, amount.0);
                Promise::new(receiver_id).function_call(
                    "on_transfer".to_string(),
                    json!({ "amount": amount }).to_string().into_bytes(),
                    0,
                    0,
                );
                ext_self::on_transfer_complete(env::current_account_id());
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect missing gas specification"
        );
        assert_eq!(findings[0].detector_id, "NEAR-012");
    }

    #[test]
    fn test_no_finding_with_gas_spec() {
        let source = r#"
            fn transfer_and_call(&mut self, receiver_id: AccountId, amount: U128) {
                self.internal_transfer(&env::predecessor_account_id(), &receiver_id, amount.0);
                Promise::new(receiver_id).function_call(
                    "on_transfer".to_string(),
                    json!({ "amount": amount }).to_string().into_bytes(),
                    0,
                    Gas(5_000_000_000_000),
                );
                ext_self::on_transfer_complete(env::current_account_id())
                    .with_static_gas(GAS_FOR_CALLBACK);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag with explicit gas specification"
        );
    }

    #[test]
    fn test_skips_callback_functions() {
        let source = r#"
            fn on_transfer_complete(&mut self) {
                Promise::new(env::predecessor_account_id()).function_call(
                    "finalize".to_string(),
                    vec![],
                    0,
                    DEFAULT_GAS,
                );
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should skip callback functions (on_ prefix)"
        );
    }

    // FP idx 0: transfer-only / batch-action Promises take no gas argument and
    // must not be flagged.
    #[test]
    fn test_no_finding_transfer_only_promise() {
        let source = r#"
            fn refund(account: AccountId, amount: Balance) {
                Promise::new(account).transfer(amount);
            }

            fn deploy_sub(name: AccountId, code: Vec<u8>) -> Promise {
                Promise::new(name)
                    .create_account()
                    .transfer(INITIAL_BALANCE)
                    .deploy_contract(code)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Batch-action Promises (transfer/create_account/deploy_contract) take no gas argument"
        );
    }

    // FP idx 1: gas supplied via a named constant not on the hard-coded allow-list.
    #[test]
    fn test_no_finding_named_gas_constant() {
        let source = r#"
            const FT_TRANSFER_GAS: Gas = Gas::from_tgas(10);

            fn send(receiver: AccountId) {
                Promise::new(receiver).function_call(
                    "ft_transfer".to_string(), vec![], 1, FT_TRANSFER_GAS,
                );
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A SCREAMING_SNAKE gas constant passed as the gas argument is an explicit spec"
        );
    }

    // FP idx 2: gas supplied through a typed function parameter.
    #[test]
    fn test_no_finding_typed_gas_param() {
        let source = r#"
            fn schedule_call(receiver: AccountId, gas_for_call: Gas) {
                Promise::new(receiver).function_call(
                    "m".to_string(), vec![], 0, gas_for_call,
                );
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A typed Gas parameter forces the caller to supply an explicit gas budget"
        );
    }

    // FP idx 3: with_unused_gas_weight is a legitimate, documented gas spec.
    #[test]
    fn test_no_finding_unused_gas_weight() {
        let source = r#"
            use near_sdk::Gas;

            fn kick_off(receiver: AccountId) {
                ext_self::ext(env::current_account_id())
                    .with_unused_gas_weight(1)
                    .finish();
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "with_unused_gas_weight explicitly allocates remaining gas by weight"
        );
    }

    // FP idx 4: "Promise::new" appearing only inside a string literal is not a call.
    #[test]
    fn test_no_finding_string_literal_promise() {
        let source = r#"
            fn log_it() {
                env::log_str("Promise::new failed downstream");
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Promise::new inside a string literal is not a cross-contract call"
        );
    }
}
