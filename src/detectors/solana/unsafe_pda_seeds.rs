use syn::visit::Visit;
use syn::ItemFn;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnsafePdaSeedsDetector;

impl Detector for UnsafePdaSeedsDetector {
    fn id(&self) -> &'static str {
        "SOL-010"
    }
    fn name(&self) -> &'static str {
        "unsafe-pda-seeds"
    }
    fn description(&self) -> &'static str {
        "Detects PDA seeds without user-specific components (collision risk)"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        let mut findings = Vec::new();
        let mut visitor = PdaVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct PdaVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for PdaVisitor<'a> {
    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();
        if fn_name.starts_with("test_") || fn_name.contains("_test") {
            return;
        }

        // Skip test functions by attribute (#[test], #[tokio::test], #[ink::test]).
        // These encode fixtures where PDA collision is irrelevant and are compiled
        // out of the deployed program.
        if has_attribute(&func.attrs, "test")
            || has_attribute(&func.attrs, "tokio::test")
            || has_attribute(&func.attrs, "ink::test")
        {
            return;
        }

        // Skip Anchor codegen/macro infrastructure functions
        let fn_lower = fn_name.to_lowercase();
        if fn_lower.contains("constraint")
            || fn_lower.contains("__anchor")
            || fn_lower.starts_with("_")
            || fn_lower.contains("seeds_with_nonce")
            || fn_lower.contains("create_with_seed")
        {
            return;
        }

        // Skip if file path suggests Anchor codegen
        let file_str = self.ctx.file_path.to_string_lossy();
        if file_str.contains("/generated/")
            || file_str.contains("/codegen/")
            || file_str.contains("constraints.rs")
            || file_str.contains("__cpi.rs")
            || file_str.contains("__client.rs")
        {
            return;
        }

        let body_src = fn_body_source(func);

        // Look for find_program_address or create_program_address calls
        if !body_src.contains("find_program_address")
            && !body_src.contains("create_program_address")
        {
            syn::visit::visit_item_fn(self, func);
            return;
        }

        // Constrain the line scan to THIS function's own source span. The whole-file
        // scan used previously flagged lines inside #[cfg(test)] modules, comments and
        // string literals belonging to other functions, and duplicated findings once
        // per qualifying function. Using the function body's brace span limits the scan
        // to lines that actually belong to this function.
        let start_line = func.block.brace_token.span.open().start().line;
        let end_line = func.block.brace_token.span.close().end().line;

        let param_names = fn_param_names(func);

        // Check each line (within this function) for PDA seed construction
        for (i, line) in self.ctx.source.lines().enumerate() {
            let line_num = i + 1;
            if line_num < start_line || line_num > end_line {
                continue;
            }
            let call_base = if line.contains("find_program_address") {
                "find_program_address"
            } else if line.contains("create_program_address") {
                "create_program_address"
            } else {
                continue;
            };

            // Get the seeds context — look at surrounding lines for the &[...] seed array
            let context = get_context_lines(&self.ctx.source, line_num, 5);

            // Classify the first argument (the seeds) of the derivation call: an inline
            // `&[...]` array literal whose contents we can see, or a bare identifier
            // (parameter / local) whose contents live elsewhere.
            let arg = seed_arg_after_call(&context, call_base);

            match arg {
                SeedArg::BareIdent(ident) => {
                    // The seed array is not an inline literal on this line. Its contents
                    // are decided elsewhere, so a lexical ±5-line window cannot see them.
                    //
                    // FP: generic pass-through helper `fn f(seeds: &[&[u8]], ...)`. If the
                    // identifier is a function parameter, the seed contents are supplied by
                    // callers; this function cannot itself exhibit a seed collision.
                    if param_names.contains(&ident) {
                        continue;
                    }
                    // FP: dynamic seed array built as a local earlier in the function
                    // (outside the ±5-line window). Scan the whole function body for a
                    // dynamic marker before flagging.
                    if contains_dynamic_seed(&body_src) {
                        continue;
                    }
                    if is_global_pda(&body_src) || is_global_pda(&context) {
                        continue;
                    }
                    self.push_finding(&fn_name, line_num, line);
                }
                SeedArg::InlineArray | SeedArg::Unknown => {
                    // Inline literal (or unrecognized form): analyze the surrounding
                    // context for dynamic/global seed markers, as before.
                    if !contains_dynamic_seed(&context) && !is_global_pda(&context) {
                        self.push_finding(&fn_name, line_num, line);
                    }
                }
            }
        }

        syn::visit::visit_item_fn(self, func);
    }
}

impl<'a> PdaVisitor<'a> {
    fn push_finding(&mut self, fn_name: &str, line_num: usize, line: &str) {
        self.findings.push(Finding {
            detector_id: "SOL-010".to_string(),
            name: "unsafe-pda-seeds".to_string(),
            severity: Severity::High,
            confidence: Confidence::Medium,
            message: format!(
                "PDA seeds in '{}' may lack user-specific components (collision risk)",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line: line_num,
            column: 1,
            snippet: line.trim().to_string(),
            recommendation: "Include user-specific seeds (e.g., user.key().as_ref()) to prevent PDA collisions. If this is an intentionally global PDA, use a named seed constant".to_string(),
            chain: Chain::Solana,
        });
    }
}

/// Classification of the first (seeds) argument of a *_program_address call.
enum SeedArg {
    /// Inline `&[...]` array literal whose element contents are visible in context.
    InlineArray,
    /// A bare identifier (function parameter or local variable) holding the seeds.
    BareIdent(String),
    /// Could not determine the argument form.
    Unknown,
}

/// Inspect the text immediately following `<call_base>(` in `context` and classify the
/// first argument. Handles the call/argument spanning multiple lines and an optional
/// leading `&`.
fn seed_arg_after_call(context: &str, call_base: &str) -> SeedArg {
    let start = match context.find(call_base) {
        Some(p) => p + call_base.len(),
        None => return SeedArg::Unknown,
    };
    let rest = &context[start..];
    let paren = match rest.find('(') {
        Some(p) => p + 1,
        None => return SeedArg::Unknown,
    };
    let after = rest[paren..].trim_start();
    // Strip an optional leading reference `&` (possibly followed by whitespace).
    let after = after.strip_prefix('&').map(|s| s.trim_start()).unwrap_or(after);

    if after.starts_with('[') {
        return SeedArg::InlineArray;
    }
    let ident: String = after
        .chars()
        .take_while(|c| c.is_alphanumeric() || *c == '_')
        .collect();
    if !ident.is_empty() && after.chars().next().map(|c| c.is_alphabetic() || c == '_') == Some(true)
    {
        return SeedArg::BareIdent(ident);
    }
    SeedArg::Unknown
}

/// Collect the names of a function's simple identifier parameters.
fn fn_param_names(func: &ItemFn) -> Vec<String> {
    func.sig
        .inputs
        .iter()
        .filter_map(|arg| {
            if let syn::FnArg::Typed(pt) = arg {
                if let syn::Pat::Ident(pi) = &*pt.pat {
                    return Some(pi.ident.to_string());
                }
            }
            None
        })
        .collect()
}

/// Whitespace-insensitive check for a dynamic (caller/user-specific) seed marker. Works
/// on both raw source and the spaced token-stream rendering of a function body.
fn contains_dynamic_seed(text: &str) -> bool {
    let norm: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    norm.contains(".key()")
        || norm.contains("as_ref()")
        || norm.contains(".to_bytes()")
        || norm.contains("to_le_bytes")
        || norm.contains("to_be_bytes")
        // String seeds: `identifier.as_bytes()` is a standard idiom (name services,
        // markets keyed by symbol, etc.) and is by construction non-constant input.
        || norm.contains("as_bytes")
        || norm.contains("user")
        || norm.contains("authority")
        || norm.contains("owner")
        || norm.contains("mint")
        || norm.contains("signer")
        || norm.contains("payer")
        || norm.contains("wallet")
        || norm.contains("sender")
        || norm.contains("recipient")
}

/// Whitespace-insensitive check for an intentionally global/singleton PDA seed.
fn is_global_pda(text: &str) -> bool {
    let norm: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    norm.contains("b\"config\"")
        || norm.contains("b\"metadata\"")
        || norm.contains("b\"state\"")
        || norm.contains("b\"global\"")
        || norm.contains("b\"treasury\"")
        || norm.contains("b\"vault\"")
        || norm.contains("b\"admin\"")
        || norm.contains("b\"program\"")
        || norm.contains("CONFIG_SEED")
        || norm.contains("STATE_SEED")
        || norm.contains("GLOBAL_SEED")
}

fn get_context_lines(source: &str, line: usize, window: usize) -> String {
    let lines: Vec<&str> = source.lines().collect();
    let start = line.saturating_sub(window + 1);
    let end = (line + window).min(lines.len());
    lines[start..end].join("\n")
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
        UnsafePdaSeedsDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_static_seeds() {
        let source = r#"
            fn create_escrow(program_id: &Pubkey) {
                let (pda, bump) = Pubkey::find_program_address(&[b"escrow"], program_id);
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect static-only PDA seeds");
    }

    #[test]
    fn test_no_finding_global_pda() {
        let source = r#"
            fn get_config(program_id: &Pubkey) {
                let (pda, bump) = Pubkey::find_program_address(&[b"config"], program_id);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag intentionally global PDAs like config"
        );
    }

    #[test]
    fn test_no_finding_with_user_key() {
        let source = r#"
            fn create_vault(program_id: &Pubkey, user: &Pubkey) {
                let (pda, bump) = Pubkey::find_program_address(
                    &[b"vault", user.key().as_ref()], program_id
                );
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag seeds with user key");
    }

    // FP #1: string seeds via `.as_bytes()` are a dynamic (caller-specific) component.
    #[test]
    fn test_no_finding_string_seed_as_bytes() {
        let source = r#"
            fn derive_name_record(name: &str, program_id: &Pubkey) -> (Pubkey, u8) {
                Pubkey::find_program_address(&[b"record", name.as_bytes()], program_id)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag PDA seeds that include a .as_bytes() string component"
        );
    }

    // FP #2: generic pass-through helper taking the seeds as a parameter. The seed
    // contents are decided at each call site, not here.
    #[test]
    fn test_no_finding_generic_seed_param() {
        let source = r#"
            fn derive_pda(seeds: &[&[u8]], program_id: &Pubkey) -> (Pubkey, u8) {
                Pubkey::find_program_address(seeds, program_id)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a pass-through helper whose seeds are a parameter"
        );
    }

    // FP #3: a static-seed derivation inside a #[cfg(test)] fixture must not be flagged
    // by the (safe) production function's scan.
    #[test]
    fn test_no_finding_static_seed_in_test_module() {
        let source = r#"
            fn create_vault(user: &Pubkey, program_id: &Pubkey) -> (Pubkey, u8) {
                Pubkey::find_program_address(&[b"vault", user.as_ref()], program_id)
            }

            #[cfg(test)]
            mod tests {
                #[test]
                fn test_static_derivation() {
                    let (pda, _) = Pubkey::find_program_address(&[b"fixture"], &crate::ID);
                    let _ = pda;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag static seeds inside a #[cfg(test)] fixture"
        );
    }

    // FP #4: dynamic seed array constructed more than 5 lines before the derivation call.
    #[test]
    fn test_no_finding_seed_built_earlier() {
        let source = r#"
            fn derive_stake(staker_key: Pubkey, program_id: &Pubkey) -> (Pubkey, u8) {
                let seeds: [&[u8]; 2] = [b"stake", staker_key.as_ref()];
                let a = 1;
                let b = 2;
                let c = 3;
                let d = 4;
                let e = 5;
                let f = a + b + c + d + e;
                let _ = f;
                Pubkey::find_program_address(&seeds, program_id)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the dynamic seed array is built earlier in the function"
        );
    }
}
