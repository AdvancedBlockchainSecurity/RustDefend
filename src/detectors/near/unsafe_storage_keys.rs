use std::collections::{HashMap, HashSet};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{Attribute, Expr, ExprCall, FnArg, ItemFn, ItemMod, Local, Macro, Pat};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct UnsafeStorageKeysDetector;

impl Detector for UnsafeStorageKeysDetector {
    fn id(&self) -> &'static str {
        "NEAR-009"
    }
    fn name(&self) -> &'static str {
        "unsafe-storage-keys"
    }
    fn description(&self) -> &'static str {
        "Detects storage key construction from user input (collision risk)"
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
        let mut visitor = StorageKeyVisitor {
            findings: &mut findings,
            ctx,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

struct StorageKeyVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
}

impl<'ast, 'a> Visit<'ast> for StorageKeyVisitor<'a> {
    fn visit_item_mod(&mut self, m: &'ast ItemMod) {
        // Never scan `#[cfg(test)]` modules — test fixture code is never
        // compiled into the deployed wasm, so it carries no on-chain
        // storage-key collision risk.
        if module_is_cfg_test(&m.attrs) {
            return;
        }
        syn::visit::visit_item_mod(self, m);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        // Skip test helpers/fixtures (#[test] / #[tokio::test] / #[ink::test]
        // and the `test_*` naming convention).
        if is_test_fn(func) {
            return;
        }

        if function_has_unsafe_storage_key(func) {
            let line = span_to_line(&func.sig.ident.span());
            let fn_name = func.sig.ident.to_string();
            self.findings.push(Finding {
                detector_id: "NEAR-009".to_string(),
                name: "unsafe-storage-keys".to_string(),
                severity: Severity::Medium,
                confidence: Confidence::Medium,
                message: format!(
                    "Function '{}' constructs storage keys from user input via format!()",
                    fn_name
                ),
                file: self.ctx.file_path.clone(),
                line,
                column: span_to_column(&func.sig.ident.span()),
                snippet: snippet_at_line(&self.ctx.source, line),
                recommendation: "Use BorshSerialize or enum-based namespacing for storage keys to prevent collisions".to_string(),
                chain: Chain::Near,
            });
        }
        // Do not recurse into the function body for further item-fn detection;
        // this matches the original top-level scanning behavior and avoids
        // double-reporting nested helpers.
    }
}

/// True if the function is a test helper/fixture that never ships on-chain.
fn is_test_fn(func: &ItemFn) -> bool {
    if func.sig.ident.to_string().starts_with("test_") {
        return true;
    }
    // Match any attribute whose final path segment is `test`
    // (`#[test]`, `#[tokio::test]`, `#[ink::test]`, ...).
    func.attrs.iter().any(|a| {
        a.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

/// True if the attribute list contains `#[cfg(test)]` (including `cfg(all(test, ...))`).
fn module_is_cfg_test(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .any(|a| a.path().is_ident("cfg") && a.meta.to_token_stream().to_string().contains("test"))
}

/// Core analysis: does this function write/read storage using a key that is
/// dynamically constructed from (potentially) user-controlled input via
/// `format!()`? Only the KEY argument of `storage_write`/`storage_read` is
/// examined — `format!` used purely for log/panic/assert messages is ignored.
fn function_has_unsafe_storage_key(func: &ItemFn) -> bool {
    let body_src = func.block.to_token_stream().to_string();

    // Backstop skip-list (preserved from the original detector): if the
    // function derives its keys via a hash or borsh serialization, the key is
    // collision-resistant / namespaced and there is nothing to flag.
    if body_src.contains("sha256")
        || body_src.contains("keccak")
        || body_src.contains("BorshSerialize")
        || body_src.contains("borsh")
    {
        return false;
    }

    let params = collect_param_idents(func);

    let mut lets: HashMap<String, Expr> = HashMap::new();
    {
        let mut lc = LetCollector { lets: &mut lets };
        lc.visit_block(&func.block);
    }

    let mut calls: Vec<ExprCall> = Vec::new();
    {
        let mut sc = StorageCallCollector { calls: &mut calls };
        sc.visit_block(&func.block);
    }

    for call in &calls {
        if let Some(key_arg) = call.args.first() {
            if matches!(analyze_key(key_arg, &params, &lets, 0), Verdict::Flag) {
                return true;
            }
        }
    }

    false
}

/// Collect the names of the function's parameters (recursing through references
/// and tuple patterns).
fn collect_param_idents(func: &ItemFn) -> HashSet<String> {
    let mut set = HashSet::new();
    for input in &func.sig.inputs {
        if let FnArg::Typed(pt) = input {
            collect_pat_idents(&pt.pat, &mut set);
        }
    }
    set
}

fn collect_pat_idents(pat: &Pat, set: &mut HashSet<String>) {
    match pat {
        Pat::Ident(pi) => {
            set.insert(pi.ident.to_string());
        }
        Pat::Reference(r) => collect_pat_idents(&r.pat, set),
        Pat::Tuple(t) => {
            for p in &t.elems {
                collect_pat_idents(p, set);
            }
        }
        Pat::TupleStruct(ts) => {
            for p in &ts.elems {
                collect_pat_idents(p, set);
            }
        }
        Pat::Type(pt) => collect_pat_idents(&pt.pat, set),
        _ => {}
    }
}

/// Collect `let NAME = <init>;` bindings within a function body, mapping the
/// bound identifier to its initializer expression. Later bindings shadow
/// earlier ones (source order).
struct LetCollector<'a> {
    lets: &'a mut HashMap<String, Expr>,
}

impl<'ast, 'a> Visit<'ast> for LetCollector<'a> {
    fn visit_local(&mut self, local: &'ast Local) {
        if let Some(name) = local_binding_name(local) {
            if let Some(init) = &local.init {
                self.lets.insert(name, (*init.expr).clone());
            }
        }
        syn::visit::visit_local(self, local);
    }
}

fn local_binding_name(local: &Local) -> Option<String> {
    match &local.pat {
        Pat::Ident(pi) => Some(pi.ident.to_string()),
        Pat::Type(pt) => {
            if let Pat::Ident(pi) = &*pt.pat {
                Some(pi.ident.to_string())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Collect calls to `env::storage_write` / `env::storage_read` (matched by the
/// final path segment, so `near_sdk::env::storage_write` also matches).
struct StorageCallCollector<'a> {
    calls: &'a mut Vec<ExprCall>,
}

impl<'ast, 'a> Visit<'ast> for StorageCallCollector<'a> {
    fn visit_expr_call(&mut self, call: &'ast ExprCall) {
        if is_storage_call(call) {
            self.calls.push(call.clone());
        }
        syn::visit::visit_expr_call(self, call);
    }
}

fn is_storage_call(call: &ExprCall) -> bool {
    if let Expr::Path(p) = &*call.func {
        if let Some(last) = p.path.segments.last() {
            let n = last.ident.to_string();
            return n == "storage_write" || n == "storage_read";
        }
    }
    false
}

enum Verdict {
    /// The key is dynamically built from non-constant input — report it.
    Flag,
    /// The key is a constant/const-only `format!` — safe.
    Safe,
    /// No `format!`-based dynamic key found on this path — nothing to say.
    Unknown,
}

/// Decide whether a storage-call key argument expression represents a
/// dynamically-constructed key. Resolves single-function `let` bindings so that
/// `let key = format!(...); storage_write(key.as_bytes(), ...)` is analyzed.
fn analyze_key(
    expr: &Expr,
    params: &HashSet<String>,
    lets: &HashMap<String, Expr>,
    depth: usize,
) -> Verdict {
    if depth > 5 {
        return Verdict::Unknown;
    }

    // Is a `format!` macro embedded directly in this key expression's subtree?
    if let Some(mac) = find_format_macro(expr) {
        return if format_is_dynamic(&mac) {
            Verdict::Flag
        } else {
            Verdict::Safe
        };
    }

    // Otherwise, if the key resolves to a local identifier, follow its binding.
    if let Some(name) = base_ident(expr) {
        if let Some(init) = lets.get(&name) {
            return analyze_key(init, params, lets, depth + 1);
        }
    }

    Verdict::Unknown
}

/// Peel trivial wrappers (`&x`, `x.as_bytes()`, `(x)`, `x?`, `x as T`, ...) to
/// find the base identifier a key expression is derived from, if any.
fn base_ident(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(p) => {
            if p.qself.is_none() && p.path.segments.len() == 1 {
                Some(p.path.segments[0].ident.to_string())
            } else {
                None
            }
        }
        Expr::MethodCall(m) => base_ident(&m.receiver),
        Expr::Reference(r) => base_ident(&r.expr),
        Expr::Paren(p) => base_ident(&p.expr),
        Expr::Group(g) => base_ident(&g.expr),
        Expr::Cast(c) => base_ident(&c.expr),
        Expr::Try(t) => base_ident(&t.expr),
        _ => None,
    }
}

/// Find the first `format!` macro anywhere within an expression subtree.
fn find_format_macro(expr: &Expr) -> Option<Macro> {
    struct F {
        found: Option<Macro>,
    }
    impl<'ast> Visit<'ast> for F {
        fn visit_macro(&mut self, m: &'ast Macro) {
            if self.found.is_none()
                && m.path
                    .segments
                    .last()
                    .map(|s| s.ident == "format")
                    .unwrap_or(false)
            {
                self.found = Some(m.clone());
            }
        }
    }
    let mut f = F { found: None };
    f.visit_expr(expr);
    f.found
}

/// True if a `format!` used to build a storage key interpolates any value that
/// is NOT a compile-time constant. A key made only of string literals and
/// SCREAMING_SNAKE_CASE consts is effectively a fixed developer-chosen key and
/// carries no user-driven collision risk.
fn format_is_dynamic(mac: &Macro) -> bool {
    let mut names = Vec::new();
    collect_names_from_tokens(mac.tokens.clone(), &mut names);
    if names.is_empty() {
        // Pure literal template (e.g. `format!("config")`) — a fixed key.
        return false;
    }
    names.iter().any(|n| !is_const_like(n))
}

/// Recursively collect identifier tokens (positional args) and inline capture
/// names embedded in string-literal templates (e.g. `{user_id}`).
fn collect_names_from_tokens(ts: TokenStream, out: &mut Vec<String>) {
    for tt in ts {
        match tt {
            TokenTree::Ident(i) => out.push(i.to_string()),
            TokenTree::Literal(l) => extract_captures(&l.to_string(), out),
            TokenTree::Group(g) => collect_names_from_tokens(g.stream(), out),
            TokenTree::Punct(_) => {}
        }
    }
}

/// Extract inline format-capture identifiers from a string literal token such
/// as `"user_{user_id}"` → `["user_id"]`. Empty/positional `{}` and format
/// specs are ignored; `{{`/`}}` escapes are handled.
fn extract_captures(lit: &str, out: &mut Vec<String>) {
    if !lit.starts_with('"') {
        return;
    }
    let inner = &lit[1..lit.len().saturating_sub(1)];
    let chars: Vec<char> = inner.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            '{' => {
                if i + 1 < chars.len() && chars[i + 1] == '{' {
                    i += 2;
                    continue;
                }
                let mut j = i + 1;
                let mut name = String::new();
                while j < chars.len() && chars[j] != '}' && chars[j] != ':' {
                    name.push(chars[j]);
                    j += 1;
                }
                while j < chars.len() && chars[j] != '}' {
                    j += 1;
                }
                let name = name.trim().to_string();
                if !name.is_empty()
                    && name
                        .chars()
                        .next()
                        .map(|c| c.is_alphabetic() || c == '_')
                        .unwrap_or(false)
                {
                    out.push(name);
                }
                i = j + 1;
            }
            '}' => {
                if i + 1 < chars.len() && chars[i + 1] == '}' {
                    i += 2;
                } else {
                    i += 1;
                }
            }
            _ => i += 1,
        }
    }
}

/// True if an identifier looks like a compile-time constant (SCREAMING_SNAKE).
fn is_const_like(n: &str) -> bool {
    n.chars()
        .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
        && n.chars().any(|c| c.is_ascii_uppercase())
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
        UnsafeStorageKeysDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_format_storage_key() {
        let source = r#"
            use near_sdk::env;
            fn store_user_data(user_id: &str, data: &[u8]) {
                let key = format!("user_{}", user_id);
                env::storage_write(key.as_bytes(), data);
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect format! in storage key");
    }

    #[test]
    fn test_detects_inline_capture_storage_key() {
        // Inline-capture form must still fire (user_id is a parameter).
        let source = r#"
            use near_sdk::env;
            fn store_user_data(user_id: &str, data: &[u8]) {
                let key = format!("user_{user_id}");
                env::storage_write(key.as_bytes(), data);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect inline-capture format! in storage key"
        );
    }

    #[test]
    fn test_no_finding_fixed_prefix() {
        let source = r#"
            use near_sdk::env;
            fn store_data(data: &[u8]) {
                env::storage_write(b"config", data);
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag fixed storage keys");
    }

    // FP0: format! only builds a log message; the key is a fixed byte literal.
    #[test]
    fn test_no_finding_format_only_in_log() {
        let source = r#"
            use near_sdk::env;
            fn set_config(data: &[u8]) {
                env::storage_write(b"config", data);
                env::log_str(&format!("config updated, {} bytes", data.len()));
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when format! feeds only a log message, not the key"
        );
    }

    // FP1: every interpolated value in the key is a compile-time constant.
    #[test]
    fn test_no_finding_const_only_format_key() {
        let source = r#"
            use near_sdk::env;
            const SCHEMA_VERSION: u32 = 2;
            fn load_state() -> Option<Vec<u8>> {
                let key = format!("state_v{}", SCHEMA_VERSION);
                env::storage_read(key.as_bytes())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a key built only from constants"
        );
    }

    // FP2: borsh enum-based key via `.try_to_vec()`; format! is only a log.
    #[test]
    fn test_no_finding_borsh_enum_key() {
        let source = r#"
            use near_sdk::env;
            use crate::StorageKey;
            fn set_metadata(self_data: Vec<u8>) {
                let key = StorageKey::Metadata.try_to_vec().unwrap();
                env::storage_write(&key, &self_data);
                env::log_str(&format!("metadata set at block {}", env::block_height()));
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag an enum-based borsh-serialized key"
        );
    }

    // FP3: test-fixture helper inside a #[cfg(test)] module.
    #[test]
    fn test_no_finding_cfg_test_module() {
        let source = r#"
            use near_sdk::env;

            #[cfg(test)]
            mod tests {
                use super::*;

                fn seed_user(id: &str) {
                    let key = format!("user_{}", id);
                    env::storage_write(key.as_bytes(), b"fixture");
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag helpers inside a #[cfg(test)] module"
        );
    }

    // FP3 (attribute variant): #[tokio::test] async test function.
    #[test]
    fn test_no_finding_tokio_test_fn() {
        let source = r#"
            use near_sdk::env;

            #[tokio::test]
            async fn seed_user() {
                let id = "alice";
                let key = format!("user_{}", id);
                env::storage_write(key.as_bytes(), b"fixture");
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag #[tokio::test] functions"
        );
    }
}
