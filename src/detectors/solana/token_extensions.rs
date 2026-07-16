use quote::ToTokens;
use std::collections::HashMap;
use syn::visit::Visit;
use syn::{
    Attribute, Expr, ExprCall, ExprMethodCall, Fields, FnArg, ItemFn, ItemMod, ItemStruct, Macro,
    PatIdent, Path,
};

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct TokenExtensionsDetector;

impl Detector for TokenExtensionsDetector {
    fn id(&self) -> &'static str {
        "SOL-012"
    }
    fn name(&self) -> &'static str {
        "token-2022-extension-safety"
    }
    fn description(&self) -> &'static str {
        "Detects programs accepting Token-2022 tokens without checking for dangerous extensions"
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
        // Skip if the file implements a transfer hook itself
        if ctx.source.contains("TransferHookExecute") {
            return Vec::new();
        }

        // Skip framework/library source files — these implement the safe wrappers
        // that user code calls; flagging them is noise, not actionable
        let file_str = ctx.file_path.to_string_lossy();
        if file_str.contains("/spl-token")
            || file_str.contains("/spl_token")
            || file_str.contains("/anchor-spl/")
            || file_str.contains("/anchor_spl/")
            || file_str.contains("/anchor/spl/")
            || file_str.contains("/token/src/")
            || file_str.contains("/token-2022/src/")
            || file_str.contains("/interface/src/")
            || file_str.contains("/anchor-lang/")
            || file_str.contains("/anchor_lang/")
            || file_str.contains("/anchor/lang/")
            || file_str.contains("/codegen/")
        {
            return Vec::new();
        }

        // Build a map of every free function in the file so we can resolve the
        // bodies of local helpers a flagged function delegates its checks to.
        let mut fc = FunctionCollector {
            functions: Vec::new(),
        };
        fc.visit_file(&ctx.ast);
        let fn_map: HashMap<String, ItemFn> = fc
            .functions
            .into_iter()
            .map(|f| (f.sig.ident.to_string(), f))
            .collect();

        // Build a map of every struct so we can inspect the Anchor #[derive(Accounts)]
        // struct that a handler's Context<T> refers to (mint-pinning constraints live there).
        let mut sc = StructCollector {
            structs: Vec::new(),
        };
        sc.visit_file(&ctx.ast);
        let struct_map: HashMap<String, ItemStruct> = sc
            .structs
            .into_iter()
            .map(|s| (s.ident.to_string(), s))
            .collect();

        let mut findings = Vec::new();
        let mut visitor = TokenExtVisitor {
            findings: &mut findings,
            ctx,
            fn_map,
            struct_map,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Strong Token-2022 signals. Their mere presence means the function is dealing
/// with the Token-2022 program (or the generic token interface), where the
/// dangerous extensions live. Note `transfer_checked` is deliberately NOT here:
/// it is the recommended instruction for the classic SPL Token program too, so
/// on its own it does not indicate Token-2022 involvement.
const TRIGGER_PATTERNS: &[&str] = &[
    "spl_token_2022",
    "Token2022",
    "InterfaceAccount",
    "token_interface",
    "TokenInterface",
];

/// A function only exposes an extension-based attack surface if it actually
/// moves/escrows tokens or performs a CPI. A pure getter/math helper over a
/// mint (e.g. reading `mint.decimals`) cannot be exploited by any extension.
const MOVEMENT_PATTERNS: &[&str] = &[
    "transfer",
    "burn",
    "mint_to",
    "CpiContext",
    "invoke",
    "withdraw",
    "deposit",
    "freeze",
    "thaw",
    "close_account",
    "approve",
    "cpi",
];

/// Token-2022 extension-introspection entry points. Counted only in *callee*
/// position (or inside a macro argument, where `require!`/`assert!` guards live)
/// — never because the word occurs somewhere in the body text.
const EXTENSION_CHECK_CALLS: &[&str] = &["get_extension_types", "assert_mint_extensions"];

/// Extension type/variant names from spl_token_2022. Code only ever writes these
/// when it is naming the extension machinery itself, so a *path segment* naming
/// one (exactly, or as a prefix — e.g. `TransferHookAccount`) is a genuine check
/// signal. Matching segments rather than raw text keeps `TransferChecked` and
/// `MintNotReady` from passing as `TransferHook` / `MintCloseAuthority`.
const EXTENSION_TYPE_PATHS: &[&str] = &[
    "ExtensionType",
    "PermanentDelegate",
    "TransferHook",
    "MintCloseAuthority",
];

/// Project-local helpers that gate which mint is acceptable. Counted only when
/// actually *called*: a local binding that merely happens to be spelled
/// `valid_mint` is a computed value, not a check. Keying on the spelling alone
/// is what silenced this detector on genuinely vulnerable escrow code.
const ALLOWLIST_HELPER_CALLS: &[&str] = &[
    "valid_mint",
    "allowed_mint",
    "mint_whitelist",
    "mint_allowlist",
];

/// Module-level allowlist consts/statics. Counted only when read as a path that
/// is not shadowed by a local binding of the same name.
const ALLOWLIST_CONSTS: &[&str] = &["ALLOWED_EXTENSION", "MINT_WHITELIST", "MINT_ALLOWLIST"];

/// Structural facts about a function, used to decide whether it really performs
/// a Token-2022 extension check rather than merely spelling one of the check's
/// vocabulary words somewhere in its body.
#[derive(Default)]
struct SafeCheckFacts {
    /// Idents in callee position (`foo(..)` and `x.foo(..)`).
    called: Vec<String>,
    /// Every path segment appearing in expression, pattern or type position.
    path_segments: Vec<String>,
    /// Bare idents inside macro invocation tokens. syn does not parse macro
    /// bodies, so `require!(!exts.contains(&ExtensionType::TransferHook), ..)`
    /// would otherwise be invisible.
    macro_idents: Vec<String>,
    /// Idents introduced by `let` bindings or parameters — local values, never a
    /// reference to a module-level allowlist const.
    locals: Vec<String>,
}

impl SafeCheckFacts {
    fn collect(func: &ItemFn) -> Self {
        let mut facts = SafeCheckFacts::default();
        facts.visit_item_fn(func);
        facts
    }

    fn is_local(&self, ident: &str) -> bool {
        self.locals.iter().any(|l| l == ident)
    }

    /// The extension API is invoked (call position, or named inside a guard macro).
    fn calls_extension_api(&self) -> bool {
        let in_calls = self
            .called
            .iter()
            .any(|c| EXTENSION_CHECK_CALLS.contains(&c.as_str()));
        let in_macros = self
            .macro_idents
            .iter()
            .any(|i| EXTENSION_CHECK_CALLS.contains(&i.as_str()) && !self.is_local(i));
        in_calls || in_macros
    }

    /// An extension type/variant is named in a real path (or guard-macro) position.
    fn names_extension_type(&self) -> bool {
        self.path_segments
            .iter()
            .chain(self.macro_idents.iter())
            .any(|seg| EXTENSION_TYPE_PATHS.iter().any(|p| seg.starts_with(p)))
    }

    /// An allowlist helper is actually called on something.
    fn calls_allowlist_helper(&self) -> bool {
        let in_calls = self
            .called
            .iter()
            .any(|c| ALLOWLIST_HELPER_CALLS.contains(&c.as_str()));
        let in_macros = self
            .macro_idents
            .iter()
            .any(|i| ALLOWLIST_HELPER_CALLS.contains(&i.as_str()) && !self.is_local(i));
        in_calls || in_macros
    }

    /// An allowlist const/static is read (and is not a shadowing local binding).
    fn reads_allowlist_const(&self) -> bool {
        self.path_segments
            .iter()
            .chain(self.macro_idents.iter())
            .any(|seg| {
                !self.is_local(seg)
                    && ALLOWLIST_CONSTS
                        .iter()
                        .any(|p| seg.to_uppercase().starts_with(p))
            })
    }
}

impl<'ast> Visit<'ast> for SafeCheckFacts {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let Expr::Path(p) = node.func.as_ref() {
            if let Some(seg) = p.path.segments.last() {
                self.called.push(seg.ident.to_string());
            }
        }
        syn::visit::visit_expr_call(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
        self.called.push(node.method.to_string());
        syn::visit::visit_expr_method_call(self, node);
    }

    fn visit_path(&mut self, node: &'ast Path) {
        for seg in &node.segments {
            self.path_segments.push(seg.ident.to_string());
        }
        syn::visit::visit_path(self, node);
    }

    fn visit_pat_ident(&mut self, node: &'ast PatIdent) {
        self.locals.push(node.ident.to_string());
        syn::visit::visit_pat_ident(self, node);
    }

    fn visit_macro(&mut self, node: &'ast Macro) {
        // Macro bodies are opaque token streams to syn; split them into bare
        // idents so guard macros still count as structural check sites.
        for piece in node
            .tokens
            .to_string()
            .split(|c: char| !(c.is_alphanumeric() || c == '_'))
        {
            if !piece.is_empty() {
                self.macro_idents.push(piece.to_string());
            }
        }
        syn::visit::visit_macro(self, node);
    }
}

/// True if `func` structurally performs a Token-2022 extension check: it invokes
/// the extension-introspection API, names an extension type/variant in a real
/// path position, calls an allowlist helper, or reads an allowlist const. A body
/// that merely mentions the vocabulary (a local `let valid_mint = ..`, a comment,
/// a string) does not qualify.
fn performs_extension_check(func: &ItemFn) -> bool {
    let facts = SafeCheckFacts::collect(func);
    facts.calls_extension_api()
        || facts.names_extension_type()
        || facts.calls_allowlist_helper()
        || facts.reads_allowlist_const()
}

/// True if the function is a test function. Covers `test_*` / `*_test` naming and
/// any attribute whose final path segment is `test` (#[test], #[tokio::test],
/// #[ink::test], #[rstest], etc.).
fn is_test_fn(fn_name: &str, attrs: &[Attribute]) -> bool {
    if fn_name.starts_with("test_") || fn_name.ends_with("_test") {
        return true;
    }
    attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .map(|s| s.ident == "test")
            .unwrap_or(false)
    })
}

/// Extract the type name `T` from the first `Context<T>` argument of a handler,
/// which is the Anchor accounts struct name.
fn context_struct_name(func: &ItemFn) -> Option<String> {
    for input in &func.sig.inputs {
        if let FnArg::Typed(pt) = input {
            let ty = pt.ty.to_token_stream().to_string();
            if let Some(idx) = ty.find("Context <") {
                let rest = &ty[idx + "Context <".len()..];
                if let Some(end) = rest.find('>') {
                    let inner = &rest[..end];
                    // inner may be "'info , Pay" or just "Pay"
                    let name = inner.split(',').last().unwrap_or("").trim().to_string();
                    if !name.is_empty() {
                        return Some(name);
                    }
                }
            }
        }
    }
    None
}

/// True if an Anchor accounts struct hard-pins the mint to a fixed address via an
/// `#[account(address = ...)]` constraint on an `InterfaceAccount<..., Mint>` field.
/// This is the canonical whitelist pattern — an attacker cannot substitute a mint
/// carrying malicious extensions, so a runtime extension scan is unnecessary.
fn struct_pins_mint(item: &ItemStruct) -> bool {
    if let Fields::Named(fields) = &item.fields {
        for field in &fields.named {
            let ty = field.ty.to_token_stream().to_string();
            if ty.contains("Mint") && has_attribute_with_value(&field.attrs, "account", "address") {
                return true;
            }
        }
    }
    false
}

/// Collects the names of functions/methods called within a block.
struct CallNameCollector {
    names: Vec<String>,
}

impl<'ast> Visit<'ast> for CallNameCollector {
    fn visit_expr_call(&mut self, node: &'ast ExprCall) {
        if let Expr::Path(p) = node.func.as_ref() {
            if let Some(seg) = p.path.segments.last() {
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

/// Collects all struct items in a file (including within modules).
struct StructCollector {
    structs: Vec<ItemStruct>,
}

impl<'ast> Visit<'ast> for StructCollector {
    fn visit_item_struct(&mut self, node: &'ast ItemStruct) {
        self.structs.push(node.clone());
        syn::visit::visit_item_struct(self, node);
    }
}

fn collect_called_fn_names(func: &ItemFn) -> Vec<String> {
    let mut c = CallNameCollector { names: Vec::new() };
    c.visit_block(&func.block);
    c.names
}

struct TokenExtVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    fn_map: HashMap<String, ItemFn>,
    struct_map: HashMap<String, ItemStruct>,
}

impl<'a> TokenExtVisitor<'a> {
    /// Resolve the local helpers this function calls (up to `depth` hops) and
    /// return true if any resolvable callee body performs the required extension
    /// check. This is a SOUND cross-function check: we only treat the code as
    /// safe when we can read the callee's body and confirm it *structurally*
    /// performs the check — never a blanket name-based skip, and never because
    /// the callee happens to spell a vocabulary word (a helper that binds
    /// `let valid_mint = mint.decimals == 6` checks decimals, not extensions).
    fn callee_has_safe_check(
        &self,
        func: &ItemFn,
        depth: usize,
        visited: &mut Vec<String>,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        for name in collect_called_fn_names(func) {
            if visited.contains(&name) {
                continue;
            }
            if let Some(callee) = self.fn_map.get(&name) {
                visited.push(name.clone());
                if performs_extension_check(callee) {
                    return true;
                }
                if self.callee_has_safe_check(callee, depth - 1, visited) {
                    return true;
                }
            }
        }
        false
    }

    /// True if the handler's Context<T> accounts struct pins the mint address.
    fn context_pins_mint(&self, func: &ItemFn) -> bool {
        if let Some(struct_name) = context_struct_name(func) {
            if let Some(item) = self.struct_map.get(&struct_name) {
                return struct_pins_mint(item);
            }
        }
        false
    }
}

impl<'ast, 'a> Visit<'ast> for TokenExtVisitor<'a> {
    fn visit_item_mod(&mut self, node: &'ast ItemMod) {
        // Skip #[cfg(test)] modules entirely — they are compiled only for host-side
        // tests, never into the deployed program, so findings on them are pure noise.
        if has_attribute_with_value(&node.attrs, "cfg", "test") {
            return;
        }
        syn::visit::visit_item_mod(self, node);
    }

    fn visit_item_fn(&mut self, func: &'ast ItemFn) {
        let fn_name = func.sig.ident.to_string();

        // Skip test functions (names and any *::test attribute path).
        if is_test_fn(&fn_name, &func.attrs) {
            return;
        }

        let fn_src = func.to_token_stream().to_string();
        let body_src = fn_body_source(func);

        // Check if token_program is constrained to spl_token v1 only
        if fn_src.contains("spl_token :: id ()") || fn_src.contains("spl_token :: ID") {
            return;
        }

        // Check for trigger patterns (strong Token-2022 signals only).
        let has_trigger = TRIGGER_PATTERNS
            .iter()
            .any(|p| body_src.contains(p) || fn_src.contains(p));

        if !has_trigger {
            return;
        }

        // Only functions that actually move/escrow tokens or perform a CPI expose an
        // extension-based attack surface. Pure getters/math over a mint are safe.
        let has_movement = MOVEMENT_PATTERNS
            .iter()
            .any(|p| body_src.contains(p) || fn_src.contains(p));

        if !has_movement {
            return;
        }

        // Check whether this function itself performs the extension check, by
        // AST structure rather than by raw text: naming an extension type in a
        // path, invoking the introspection API, or calling an allowlist helper.
        if performs_extension_check(func) {
            return;
        }

        // The extension check may be delegated to a local helper. Resolve callee
        // bodies (up to 2 hops) and confirm the check tokens are actually present.
        if self.callee_has_safe_check(func, 2, &mut Vec::new()) {
            return;
        }

        // The mint may be hard-pinned to a fixed address by the Anchor accounts
        // struct referenced through Context<T>; that is the canonical whitelist.
        if self.context_pins_mint(func) {
            return;
        }

        let line = span_to_line(&func.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "SOL-012".to_string(),
            name: "token-2022-extension-safety".to_string(),
            severity: Severity::High,
            confidence: Confidence::Medium,
            message: format!(
                "Function '{}' accepts Token-2022 tokens without checking for dangerous extensions (PermanentDelegate, TransferHook, MintCloseAuthority)",
                fn_name
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&func.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Check mint extensions via get_extension_types() and reject mints with PermanentDelegate, TransferHook, or MintCloseAuthority extensions".to_string(),
            chain: Chain::Solana,
        });
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
        TokenExtensionsDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_token2022_without_extension_check() {
        let source = r#"
            fn process_transfer(mint: &InterfaceAccount<Mint>, from: &InterfaceAccount<TokenAccount>) {
                let cpi_ctx = CpiContext::new(token_program.to_account_info(), Transfer {
                    from: from.to_account_info(),
                    to: to.to_account_info(),
                    authority: authority.to_account_info(),
                });
                transfer_checked(cpi_ctx, amount, mint.decimals)?;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect Token-2022 without extension check"
        );
        assert_eq!(findings[0].detector_id, "SOL-012");
    }

    #[test]
    fn test_no_finding_with_extension_check() {
        let source = r#"
            fn process_transfer(mint: &InterfaceAccount<Mint>) {
                let extensions = get_extension_types(&mint.to_account_info().data.borrow())?;
                if extensions.contains(&ExtensionType::PermanentDelegate) {
                    return Err(ErrorCode::UnsupportedExtension.into());
                }
                transfer_checked(cpi_ctx, amount, mint.decimals)?;
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when extension check is present"
        );
    }

    #[test]
    fn test_no_finding_with_spl_token_v1_only() {
        let source = r#"
            fn process_transfer(token_program: AccountInfo) {
                // token_program constrained to spl_token :: ID
                assert_eq!(token_program.key, &spl_token :: ID);
                transfer_checked(cpi_ctx, amount, decimals);
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when constrained to spl_token v1"
        );
    }

    // FP idx 0: transfer_checked used with classic SPL Token v1. No strong
    // Token-2022 signal appears in the handler (the constraint lives in the
    // Program<'info, Token> accounts field), so it must not be flagged.
    #[test]
    fn test_no_finding_classic_token_transfer_checked() {
        let source = r#"
            #[derive(Accounts)]
            pub struct Withdraw<'info> {
                pub token_program: Program<'info, Token>,
                pub mint: Account<'info, Mint>,
            }

            pub fn withdraw(ctx: Context<Withdraw>, amount: u64) -> Result<()> {
                let cpi_ctx = CpiContext::new(
                    ctx.accounts.token_program.to_account_info(),
                    anchor_spl::token::TransferChecked {
                        from: ctx.accounts.vault.to_account_info(),
                        mint: ctx.accounts.mint.to_account_info(),
                        to: ctx.accounts.user_ata.to_account_info(),
                        authority: ctx.accounts.vault_authority.to_account_info(),
                    },
                );
                anchor_spl::token::transfer_checked(cpi_ctx, amount, ctx.accounts.mint.decimals)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag classic SPL Token transfer_checked without a Token-2022 signal"
        );
    }

    // FP idx 1: extension check delegated to a local helper. The callee body is
    // resolved and confirmed to reject dangerous extensions, so deposit is safe.
    #[test]
    fn test_no_finding_extension_check_in_helper() {
        let source = r#"
            fn validate_mint_extensions(mint: &InterfaceAccount<Mint>) -> Result<()> {
                let data = mint.to_account_info().data.borrow();
                let state = StateWithExtensions::<Mint>::unpack(&data)?;
                for ext in state.get_extension_types()? {
                    match ext {
                        ExtensionType::PermanentDelegate | ExtensionType::TransferHook => {
                            return Err(ErrorCode::UnsupportedExtension.into())
                        }
                        _ => {}
                    }
                }
                Ok(())
            }

            pub fn deposit(ctx: Context<Deposit>, amount: u64) -> Result<()> {
                validate_mint_extensions(&ctx.accounts.mint)?;
                token_interface::transfer_checked(cpi_ctx(&ctx), amount, ctx.accounts.mint.decimals)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a resolvable helper performs the extension check"
        );
    }

    // MUST STILL FLAG (regression guard for ADV-206).
    //
    // `deposit` escrows an attacker-supplied Token-2022 mint via transfer_checked
    // after delegating to a helper that only sanity-checks decimals and supply.
    // The helper binds its result to a local named `valid_mint` — a word from the
    // old safe-pattern vocabulary — but names nothing from the Token-2022
    // extension API and calls no allowlist helper, so it cannot reject a mint
    // carrying PermanentDelegate or TransferHook. Under raw substring matching
    // that local silenced the detector on genuinely vulnerable code; renaming it
    // to `decimals_ok` made the exact same vulnerability fire. The finding must
    // not depend on what a local variable is spelled.
    #[test]
    fn test_still_flags_helper_that_only_spells_valid_mint() {
        let source = r#"
            fn ensure_mint_ready(mint: &InterfaceAccount<Mint>) -> Result<()> {
                let valid_mint = mint.decimals == 6 && mint.supply > 0;
                if !valid_mint {
                    return Err(EscrowError::MintNotReady.into());
                }
                Ok(())
            }

            pub fn deposit(ctx: Context<Deposit>, amount: u64) -> Result<()> {
                ensure_mint_ready(&ctx.accounts.mint)?;
                let cpi_ctx = CpiContext::new(
                    ctx.accounts.token_program.to_account_info(),
                    TransferChecked {
                        from: ctx.accounts.depositor_ata.to_account_info(),
                        mint: ctx.accounts.mint.to_account_info(),
                        to: ctx.accounts.vault.to_account_info(),
                        authority: ctx.accounts.depositor.to_account_info(),
                    },
                );
                token_interface::transfer_checked(cpi_ctx, amount, ctx.accounts.mint.decimals)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.detector_id == "SOL-012"),
            "Must flag: helper only checks decimals/supply, a local named `valid_mint` is not an extension check"
        );
    }

    // MUST STILL FLAG: the same vulnerability with the local renamed. This is the
    // control for the test above — both spellings must produce the same finding.
    #[test]
    fn test_still_flags_helper_with_renamed_local() {
        let source = r#"
            fn ensure_mint_ready(mint: &InterfaceAccount<Mint>) -> Result<()> {
                let decimals_ok = mint.decimals == 6 && mint.supply > 0;
                if !decimals_ok {
                    return Err(EscrowError::MintNotReady.into());
                }
                Ok(())
            }

            pub fn deposit(ctx: Context<Deposit>, amount: u64) -> Result<()> {
                ensure_mint_ready(&ctx.accounts.mint)?;
                token_interface::transfer_checked(cpi_ctx(&ctx), amount, ctx.accounts.mint.decimals)?;
                Ok(())
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.detector_id == "SOL-012"),
            "Must flag: renaming a local must not change whether the vuln is reported"
        );
    }

    // A `require!` guard naming an extension type is a real check even though syn
    // does not parse macro bodies into paths.
    #[test]
    fn test_no_finding_extension_check_inside_require_macro() {
        let source = r#"
            pub fn deposit(ctx: Context<Deposit>, amount: u64) -> Result<()> {
                let exts = get_extension_types(&ctx.accounts.mint.to_account_info().data.borrow())?;
                require!(!exts.contains(&ExtensionType::TransferHook), ErrorCode::BadMint);
                token_interface::transfer_checked(cpi_ctx(&ctx), amount, ctx.accounts.mint.decimals)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when a require! guard rejects a dangerous extension"
        );
    }

    // FP idx 2: pure view/computation function that merely mentions InterfaceAccount.
    #[test]
    fn test_no_finding_pure_view_function() {
        let source = r#"
            fn ui_amount_to_base(mint: &InterfaceAccount<Mint>, ui_amount: f64) -> u64 {
                (ui_amount * 10f64.powi(mint.decimals as i32)) as u64
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag a pure read/computation helper that moves no tokens"
        );
    }

    // FP idx 3: mint pinned to a fixed address via an Anchor account constraint.
    #[test]
    fn test_no_finding_mint_pinned_by_address_constraint() {
        let source = r#"
            #[derive(Accounts)]
            pub struct Pay<'info> {
                #[account(address = USDC_MINT @ ErrorCode::WrongMint)]
                pub mint: InterfaceAccount<'info, Mint>,
                pub token_program: Interface<'info, TokenInterface>,
            }

            pub fn pay(ctx: Context<Pay>, amount: u64) -> Result<()> {
                token_interface::transfer_checked(cpi_ctx(&ctx), amount, ctx.accounts.mint.decimals)
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when the mint is hard-pinned by an address constraint"
        );
    }

    // FP idx 4: test-only helpers and #[tokio::test] functions under #[cfg(test)].
    #[test]
    fn test_no_finding_cfg_test_module() {
        let source = r#"
            #[cfg(test)]
            mod tests {
                async fn setup_token2022_mint(ctx: &mut ProgramTestContext) -> Pubkey {
                    create_mint(ctx, &spl_token_2022::id()).await
                }

                #[tokio::test]
                async fn transfers_work() {
                    let mint = setup_token2022_mint(&mut ctx).await;
                    token_interface::transfer_checked(cpi, 1, 2);
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag functions inside a #[cfg(test)] module"
        );
    }
}
