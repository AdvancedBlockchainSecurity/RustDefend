use std::collections::{HashMap, HashSet};

use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::visit::Visit;
use syn::ItemFn;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct LookupTableDetector;

impl Detector for LookupTableDetector {
    fn id(&self) -> &'static str {
        "SOL-015"
    }
    fn name(&self) -> &'static str {
        "lookup-table-manipulation"
    }
    fn description(&self) -> &'static str {
        "Detects AddressLookupTableAccount usage without authority or freeze verification"
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
        // Quick check: skip files that don't mention lookup tables at all
        if !ctx.source.contains("AddressLookupTableAccount")
            && !ctx.source.contains("LookupTableAccount")
        {
            return Vec::new();
        }

        // Skip files that are test files by path (integration tests / *_test.rs).
        // Their transaction builders operate on fixtures, never on-chain input.
        if is_test_file_path(&ctx.file_path) {
            return Vec::new();
        }

        // Pre-build a map of every function's (literal-stripped) body source so we
        // can resolve validation that was factored out into a directly-called local
        // helper (idx 2). Using the crate call graph is only sound intra-file here,
        // so we resolve against functions parsed in this file.
        let mut fc = FunctionCollector {
            functions: Vec::new(),
        };
        fc.visit_file(&ctx.ast);
        let mut fn_bodies: HashMap<String, String> = HashMap::new();
        for f in &fc.functions {
            fn_bodies
                .entry(f.sig.ident.to_string())
                .or_insert_with(|| code_string_of(&f.block.to_token_stream()));
        }

        // Names of const/static items in the file — used to recognise a
        // hardcoded, operator-owned lookup-table key (idx 0).
        let const_set = collect_const_names(&ctx.ast);

        let mut findings = Vec::new();
        let mut visitor = LookupTableVisitor {
            findings: &mut findings,
            ctx,
            fn_bodies: &fn_bodies,
            const_set: &const_set,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

const TRIGGER_PATTERNS: &[&str] = &["AddressLookupTableAccount", "LookupTableAccount"];

const SAFE_PATTERNS: &[&str] = &[
    "meta.authority",
    "meta . authority",
    "freeze_authority",
    "is_frozen",
    "lookup_table.meta",
    "lookup_table . meta",
];

const TRANSACTION_PATTERNS: &[&str] = &[
    "VersionedTransaction",
    "MessageV0",
    "v0::Message",
    "address_lookup_table_accounts",
    "compile_v0",
    "new_v0",
];

struct LookupTableVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    fn_bodies: &'a HashMap<String, String>,
    const_set: &'a HashSet<String>,
}

impl<'ast, 'a> Visit<'ast> for LookupTableVisitor<'a> {
    fn visit_item_mod(&mut self, module: &'ast syn::ItemMod) {
        // Do not descend into `#[cfg(test)]` modules: their helpers build
        // transactions from dummy fixtures, never from attacker input (idx 1).
        if attrs_have_cfg_test(&module.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, module);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions
        if fn_name.starts_with("test_")
            || fn_name.ends_with("_test")
            || has_attribute(&func.attrs, "test")
            || attrs_have_cfg_test(&func.attrs)
        {
            return;
        }

        // Literal-stripped code view: doc comments (which live as `#[doc = "..."]`
        // string literals in the token stream) and ordinary string/char literals are
        // blanked, so trigger/transaction patterns only match real code (idx 3).
        let code_src = code_string_of(&func.to_token_stream());

        // Keep the raw token-stream views for the (unchanged) string-literal-based
        // safe-pattern matching.
        let fn_src = func.to_token_stream().to_string();
        let body_src = fn_body_source(func);

        // Check for trigger patterns (real code only)
        let has_trigger = TRIGGER_PATTERNS.iter().any(|p| code_src.contains(p));

        if !has_trigger {
            return;
        }

        // Check for safe authority/freeze patterns performed in this function.
        let has_safe_local = SAFE_PATTERNS
            .iter()
            .any(|p| body_src.contains(p) || fn_src.contains(p));

        // Authority check written by destructuring `LookupTableMeta { authority, .. }`
        // rather than chained `.meta.authority` field access (idx 4).
        let has_destructured_meta_check = code_src.contains("LookupTableMeta")
            && (code_src.contains("authority")
                || code_src.contains("is_frozen")
                || code_src.contains("deactivation_slot"));

        if has_safe_local || has_destructured_meta_check {
            return;
        }

        // Authority/freeze verification factored into a directly-called local helper
        // (idx 2): resolve the callee's body and confirm it actually contains one of
        // the required check tokens before treating this function as safe.
        for callee in called_free_fns(func) {
            if let Some(callee_body) = self.fn_bodies.get(&callee) {
                if SAFE_PATTERNS.iter().any(|p| callee_body.contains(p)) {
                    return;
                }
            }
        }

        // Check if the lookup table is used in a transaction context
        let in_tx_context = TRANSACTION_PATTERNS.iter().any(|p| code_src.contains(p));

        if !in_tx_context {
            return;
        }

        // Off-chain client idiom (idx 0): the SDK convenience struct
        // `AddressLookupTableAccount { key, addresses }` is constructed inline from a
        // hardcoded, operator-owned const key inside client code (RpcClient present).
        // The key is not attacker-controlled, and the addresses come straight from the
        // deserialized on-chain account, so there is no manipulation vector. This does
        // NOT match a builder that receives the lookup table as an untrusted parameter.
        if code_src.contains("RpcClient") && constructs_const_key_lut(func, self.const_set) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-015".to_string(),
            name: "lookup-table-manipulation".to_string(),
            severity: Severity::High,
            confidence: Confidence::Medium,
            message: format!(
                "Function '{}' uses AddressLookupTableAccount in transaction context without verifying authority or freeze status",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Verify lookup table authority and freeze status before using in transactions to prevent manipulation attacks".to_string(),
            chain: Chain::Solana,
        });
    }
}

/// Build a searchable string from a token stream, blanking the contents of
/// string / char / byte / raw-string literals. Doc comments (`///`) are encoded
/// as `#[doc = "..."]` string literals in the token stream, so they are blanked
/// too. Numeric literals are preserved. Spacing matches proc_macro2's Display,
/// so it stays consistent with the existing space-separated pattern strings.
fn strip_string_literals(ts: TokenStream) -> TokenStream {
    use proc_macro2::{Group, Literal, TokenTree};
    ts.into_iter()
        .map(|tt| match tt {
            TokenTree::Group(g) => {
                let inner = strip_string_literals(g.stream());
                TokenTree::Group(Group::new(g.delimiter(), inner))
            }
            TokenTree::Literal(lit) => {
                let s = lit.to_string();
                let first = s.chars().next().unwrap_or(' ');
                // string ("), char/lifetime-free char ('), byte/byte-str (b),
                // raw / raw-byte string (r) — blank them all.
                if first == '"' || first == '\'' || first == 'b' || first == 'r' {
                    TokenTree::Literal(Literal::string(""))
                } else {
                    TokenTree::Literal(lit)
                }
            }
            other => other,
        })
        .collect()
}

fn code_string_of(ts: &TokenStream) -> String {
    strip_string_literals(ts.clone()).to_string()
}

/// True if the attribute list contains a `#[cfg(... test ...)]` attribute.
fn attrs_have_cfg_test(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        attr.path().is_ident("cfg") && attr.to_token_stream().to_string().contains("test")
    })
}

/// True if this file path denotes test code (integration tests dir or *_test.rs).
fn is_test_file_path(path: &std::path::Path) -> bool {
    let s = path.to_string_lossy();
    s.contains("/tests/") || s.contains("\\tests\\") || s.ends_with("_test.rs")
}

/// Collect the names of all const/static items declared anywhere in the file.
fn collect_const_names(ast: &syn::File) -> HashSet<String> {
    struct C {
        names: HashSet<String>,
    }
    impl<'ast> Visit<'ast> for C {
        fn visit_item_const(&mut self, i: &'ast syn::ItemConst) {
            self.names.insert(i.ident.to_string());
            syn::visit::visit_item_const(self, i);
        }
        fn visit_item_static(&mut self, i: &'ast syn::ItemStatic) {
            self.names.insert(i.ident.to_string());
            syn::visit::visit_item_static(self, i);
        }
    }
    let mut c = C {
        names: HashSet::new(),
    };
    c.visit_file(ast);
    c.names
}

/// True for an identifier that looks like a constant (SCREAMING_SNAKE_CASE).
fn is_const_like_ident(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        && s.chars().any(|c| c.is_ascii_uppercase())
}

/// True if the function constructs `AddressLookupTableAccount { key: <K>, .. }`
/// where `<K>` is a hardcoded constant (a const/static item, or SCREAMING_SNAKE).
fn constructs_const_key_lut(func: &ItemFn, const_set: &HashSet<String>) -> bool {
    struct V<'a> {
        found: bool,
        consts: &'a HashSet<String>,
    }
    impl<'ast, 'a> Visit<'ast> for V<'a> {
        fn visit_expr_struct(&mut self, node: &'ast syn::ExprStruct) {
            let is_lut = node
                .path
                .segments
                .last()
                .map(|s| s.ident == "AddressLookupTableAccount")
                .unwrap_or(false);
            if is_lut {
                for field in &node.fields {
                    if let syn::Member::Named(m) = &field.member {
                        if m == "key" {
                            if let syn::Expr::Path(p) = &field.expr {
                                if let Some(seg) = p.path.segments.last() {
                                    let id = seg.ident.to_string();
                                    if is_const_like_ident(&id) || self.consts.contains(&id) {
                                        self.found = true;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            syn::visit::visit_expr_struct(self, node);
        }
    }
    let mut v = V {
        found: false,
        consts: const_set,
    };
    v.visit_item_fn(func);
    v.found
}

/// Collect the names of free-function (path) calls made directly in a function
/// body. Method calls are intentionally ignored — we only resolve local helpers.
fn called_free_fns(func: &ItemFn) -> Vec<String> {
    struct C {
        names: Vec<String>,
    }
    impl<'ast> Visit<'ast> for C {
        fn visit_expr_call(&mut self, node: &'ast syn::ExprCall) {
            if let syn::Expr::Path(p) = node.func.as_ref() {
                if let Some(id) = p.path.get_ident() {
                    self.names.push(id.to_string());
                } else if let Some(seg) = p.path.segments.last() {
                    self.names.push(seg.ident.to_string());
                }
            }
            syn::visit::visit_expr_call(self, node);
        }
    }
    let mut c = C { names: Vec::new() };
    c.visit_item_fn(func);
    c.names
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
        LookupTableDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_lookup_table_without_authority_check() {
        let source = r#"
            fn build_versioned_tx(lookup_table: AddressLookupTableAccount) {
                let accounts = vec![lookup_table];
                let msg = MessageV0::try_compile(
                    &payer.pubkey(),
                    &instructions,
                    &accounts,
                    recent_blockhash,
                )?;
                let tx = VersionedTransaction::try_new(msg, &[&payer])?;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect lookup table usage without authority check"
        );
        assert_eq!(findings[0].detector_id, "SOL-015");
    }

    #[test]
    fn test_no_finding_with_authority_check() {
        let source = r#"
            fn build_versioned_tx(lookup_table: AddressLookupTableAccount) {
                if lookup_table.meta.authority != Some(expected_authority) {
                    return Err(Error::InvalidAuthority);
                }
                let accounts = vec![lookup_table];
                let msg = MessageV0::try_compile(
                    &payer.pubkey(),
                    &instructions,
                    &accounts,
                    recent_blockhash,
                )?;
                let tx = VersionedTransaction::try_new(msg, &[&payer])?;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when authority check is present"
        );
    }

    // idx 0: canonical client-side v0 builder with a hardcoded, operator-owned
    // lookup-table const key. Not attacker-controlled -> no manipulation vector.
    #[test]
    fn test_no_finding_offchain_client_const_key_lut() {
        let source = r#"
            const OUR_LUT: Pubkey = SOME_TABLE;

            async fn send_swap(client: &RpcClient, payer: &Keypair) -> Result<Signature> {
                let raw = client.get_account(&OUR_LUT).await?;
                let table = AddressLookupTable::deserialize(&raw.data)?;
                let lut = AddressLookupTableAccount { key: OUR_LUT, addresses: table.addresses.to_vec() };
                let msg = v0::Message::try_compile(&payer.pubkey(), &instructions, &[lut], blockhash)?;
                let tx = VersionedTransaction::try_new(msg, &[payer])?;
                client.send_transaction(&tx).await
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag off-chain client builder using a hardcoded const LUT key"
        );
    }

    // idx 1: helper inside a #[cfg(test)] module builds a fixture transaction.
    #[test]
    fn test_no_finding_cfg_test_module_helper() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                fn make_v0_tx_fixture(lut: AddressLookupTableAccount) -> VersionedTransaction {
                    let msg = MessageV0::try_compile(&payer.pubkey(), &ixs, &[lut], blockhash).unwrap();
                    VersionedTransaction::try_new(msg, &[&payer]).unwrap()
                }

                #[test]
                fn test_swap() {
                    let _tx = make_v0_tx_fixture(dummy_lut());
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag transaction builders inside #[cfg(test)] modules"
        );
    }

    // idx 2: authority verification factored into a directly-called local helper.
    #[test]
    fn test_no_finding_authority_check_in_called_helper() {
        let source = r#"
            fn assert_lut_trusted(state: &AddressLookupTable) -> Result<()> {
                require!(state.meta.authority == Some(ADMIN), Error::BadAuthority);
                Ok(())
            }

            fn build_tx(key: Pubkey, state: AddressLookupTable) -> Result<VersionedTransaction> {
                assert_lut_trusted(&state)?;
                let lut = AddressLookupTableAccount { key, addresses: state.addresses.to_vec() };
                let msg = MessageV0::try_compile(&payer.pubkey(), &ixs, &[lut], blockhash)?;
                Ok(VersionedTransaction::try_new(msg, &[&payer])?)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a called helper performs the authority check"
        );
    }

    // idx 2 negative control: a called helper that does NOT check authority must
    // still leave the finding in place (no blanket name-based skip).
    #[test]
    fn test_still_fires_when_called_helper_has_no_check() {
        let source = r#"
            fn assert_lut_trusted(state: &AddressLookupTable) -> Result<()> {
                log_something(state);
                Ok(())
            }

            fn build_tx(key: Pubkey, state: AddressLookupTable) -> Result<VersionedTransaction> {
                assert_lut_trusted(&state)?;
                let lut = AddressLookupTableAccount { key, addresses: state.addresses.to_vec() };
                let msg = MessageV0::try_compile(&payer.pubkey(), &ixs, &[lut], blockhash)?;
                Ok(VersionedTransaction::try_new(msg, &[&payer])?)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should still fire when the called helper performs no authority check"
        );
    }

    // idx 3: trigger/transaction strings appear only in a doc comment and an error
    // string literal; the function uses no lookup table (empty LUT slice).
    #[test]
    fn test_no_finding_trigger_only_in_doc_and_string() {
        let source = r#"
            /// Compiles a v0 message from addresses extracted from a pre-verified
            /// AddressLookupTableAccount upstream.
            fn compile_from_verified(addresses: &[Pubkey]) -> Result<MessageV0> {
                if addresses.is_empty() {
                    return Err(anyhow!("compile_v0 requires at least one address"));
                }
                MessageV0::try_compile(&payer.pubkey(), &build_ixs(addresses), &[], blockhash)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when trigger patterns appear only in doc comments / string literals"
        );
    }

    // idx 4: authority check written by destructuring LookupTableMeta.
    #[test]
    fn test_no_finding_destructured_meta_authority_check() {
        let source = r#"
            fn build_tx(key: Pubkey, state: AddressLookupTable) -> Result<VersionedTransaction> {
                let LookupTableMeta { authority, .. } = state.meta;
                if authority != Some(EXPECTED_AUTHORITY) {
                    return Err(Error::InvalidAuthority);
                }
                let lut = AddressLookupTableAccount { key, addresses: state.addresses.to_vec() };
                let msg = MessageV0::try_compile(&payer.pubkey(), &ixs, &[lut], blockhash)?;
                Ok(VersionedTransaction::try_new(msg, &[&payer])?)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when authority is checked via LookupTableMeta destructuring"
        );
    }
}
