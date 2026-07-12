use std::collections::HashMap;

use quote::ToTokens;
use syn::visit::Visit;
use syn::ImplItemFn;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use crate::utils::ast_helpers::*;

pub struct MissingCallerCheckDetector;

impl Detector for MissingCallerCheckDetector {
    fn id(&self) -> &'static str {
        "INK-003"
    }
    fn name(&self) -> &'static str {
        "ink-missing-caller-check"
    }
    fn description(&self) -> &'static str {
        "Detects #[ink(message)] functions that write storage without caller check"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Ink
    }

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Pre-build a map of every impl method's name -> tokenized body in this
        // file. This lets us RESOLVE private access-control guard helpers
        // (e.g. `self.ensure_admin()?`) that are invoked from a message body,
        // which the top-level `build_call_graph` intentionally does not cover.
        let mut method_collector = MethodBodyCollector {
            bodies: HashMap::new(),
        };
        method_collector.visit_file(&ctx.ast);

        let mut findings = Vec::new();
        let mut visitor = CallerVisitor {
            findings: &mut findings,
            ctx,
            method_bodies: &method_collector.bodies,
        };
        visitor.visit_file(&ctx.ast);
        findings
    }
}

/// Collects `name -> tokenized body` for every impl method in the file so that
/// helper calls can be resolved to their actual bodies.
struct MethodBodyCollector {
    bodies: HashMap<String, String>,
}

impl<'ast> Visit<'ast> for MethodBodyCollector {
    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        let name = method.sig.ident.to_string();
        let body = method.block.to_token_stream().to_string();
        self.bodies.entry(name).or_insert(body);
        syn::visit::visit_impl_item_fn(self, method);
    }
}

struct CallerVisitor<'a> {
    findings: &'a mut Vec<Finding>,
    ctx: &'a ScanContext,
    /// name -> tokenized body for every impl method in this file.
    method_bodies: &'a HashMap<String, String>,
}

impl<'ast, 'a> Visit<'ast> for CallerVisitor<'a> {
    fn visit_impl_item_fn(&mut self, method: &'ast ImplItemFn) {
        // Check for #[ink(message)] attribute, and record OpenBrush-style
        // attribute access-control modifiers (#[modifiers(only_owner)]).
        let mut has_ink_message = false;
        let mut is_payable = false;
        let mut has_modifier_guard = false;
        for attr in &method.attrs {
            let tokens = attr.meta.to_token_stream().to_string();
            if tokens.contains("ink") && tokens.contains("message") {
                has_ink_message = true;
                if tokens.contains("payable") {
                    is_payable = true;
                }
            }
            // OpenBrush / ink-brush modifier macros wrap the body in an access
            // control check that reverts for unauthorized callers before any
            // storage write runs. Such an attribute cannot appear on a
            // genuinely unguarded method, so recognizing it loses no true
            // positives.
            if tokens.contains("modifiers")
                && (tokens.contains("only_owner")
                    || tokens.contains("only_role")
                    || tokens.contains("only_admin")
                    || tokens.contains("only_owner_or")
                    || tokens.contains("only_role_or")
                    || tokens.contains("access_control"))
            {
                has_modifier_guard = true;
            }
        }

        if !has_ink_message {
            return;
        }

        // FP idx 1: access control applied via attribute modifier.
        if has_modifier_guard {
            return;
        }

        // Only check methods that take &mut self (can actually write storage)
        let sig_src = method.sig.to_token_stream().to_string();
        if !sig_src.contains("& mut self") && !sig_src.contains("&mut self") {
            return;
        }

        let method_name = method.sig.ident.to_string();
        let name_lower = method_name.to_lowercase();

        // Skip known permissionless patterns — standard interface methods and trivial operations
        if name_lower == "flip"
            || name_lower == "inc"
            || name_lower == "increment"
            || name_lower == "decrement"
            || name_lower == "vote"
            || name_lower == "register"
            || name_lower == "new"
            || name_lower.starts_with("get_")
            || name_lower.starts_with("is_")
            || name_lower.starts_with("has_")
        {
            return;
        }

        // Skip PSP22/PSP34 (ERC-20/721 equivalent) standard interface methods
        if name_lower == "transfer"
            || name_lower == "transfer_from"
            || name_lower == "approve"
            || name_lower == "increase_allowance"
            || name_lower == "decrease_allowance"
        {
            return;
        }

        let body_src = method.block.to_token_stream().to_string();

        // Check for actual storage mutation patterns: `self.field = value`
        // (assignment to a self place). This precisely parses the assignment
        // target so match arms (`=>`), comparisons (`==`, `>=`, `<=`, `!=`) and
        // right-hand-side reads of `self.x` are NOT mistaken for writes.
        let writes = self_field_writes(&body_src);
        let has_storage_write = !writes.is_empty();

        if !has_storage_write {
            return;
        }

        // Check for caller verification in the method's own body.
        let mut has_caller_check = body_contains_caller_check(&body_src);

        // FP idx 0: access control delegated to a private guard helper such as
        // `self.ensure_admin()?` or `if !self.is_admin() { ... }`. Resolve the
        // called helper's actual body (same-file impl method) and only treat
        // the method as checked if a resolved helper genuinely performs a
        // caller check. Unresolvable helpers are NOT treated as safe, so no
        // true positive is silenced by a blanket name-based skip.
        if !has_caller_check {
            let called = extract_self_method_calls(&body_src);
            let mut visited: Vec<String> = Vec::new();
            if called
                .iter()
                .any(|callee| resolved_call_has_check(self.method_bodies, callee, &mut visited, 0))
            {
                has_caller_check = true;
            }
        }

        if has_caller_check {
            return;
        }

        // Determine risk level based on what's being written and method context
        let has_value_transfer = body_src.contains("transfer (")
            || body_src.contains("transfer(")
            || body_src.contains("transferred_value");

        // High-risk field writes: admin/owner/config fields
        let written_fields: Vec<String> = writes.iter().map(|(f, _)| f.clone()).collect();
        let has_sensitive_write = written_fields.iter().any(|f| is_sensitive_field(f));

        // FP idx 3: permissionless keeper/sync methods whose every stored value
        // is an environment-derived quantity the caller cannot influence
        // (block timestamp / block number). There is no caller privilege to
        // protect at such a write site. Requires every write to be env-derived
        // and no sensitive field / value transfer, so mixed writes that store a
        // caller-controlled value still fire.
        if !has_value_transfer && !has_sensitive_write && all_writes_env_derived(&writes) {
            return;
        }

        // FP idx 4: state/deadline transition guarded by an early return
        // (`if cond { return Err(..) }`) placed before the first storage write,
        // rather than an assert!/ensure!. This is equivalent to the assert!
        // guard the detector already accepts. Restricted to non-sensitive,
        // non-value-transfer writes so privileged writes keep full detection.
        if !has_value_transfer && !has_sensitive_write && has_early_return_guard(&body_src) {
            return;
        }

        // Caller-scoped writes: mapping insert keyed by caller
        let has_caller_scoped_write = body_src.contains("env () . caller")
            || body_src.contains("env() . caller")
            || body_src.contains("env().caller");

        // Determine severity and confidence based on risk signals
        let (severity, confidence, extra_context) = if has_value_transfer {
            // Transferring value without auth is always Critical
            (Severity::Critical, Confidence::High, " (transfers value)")
        } else if has_sensitive_write {
            // Writing to admin/owner fields without auth is Critical
            (
                Severity::Critical,
                Confidence::High,
                " (modifies sensitive field)",
            )
        } else if has_caller_scoped_write || is_payable {
            // Caller-scoped or payable methods are low risk
            (
                Severity::Medium,
                Confidence::Low,
                " (likely permissionless by design)",
            )
        } else {
            // General storage write — flag but at reduced confidence
            (Severity::High, Confidence::Medium, "")
        };

        let line = span_to_line(&method.sig.ident.span());
        self.findings.push(Finding {
            detector_id: "INK-003".to_string(),
            name: "ink-missing-caller-check".to_string(),
            severity,
            confidence,
            message: format!(
                "#[ink(message)] '{}' writes to storage without verifying caller{}",
                method_name, extra_context
            ),
            file: self.ctx.file_path.clone(),
            line,
            column: span_to_column(&method.sig.ident.span()),
            snippet: snippet_at_line(&self.ctx.source, line),
            recommendation: "Add `assert_eq!(self.env().caller(), self.owner)` or similar caller verification before storage writes".to_string(),
            chain: Chain::Ink,
        });
    }
}

/// True if a field name looks like a privileged/sensitive access-control field.
fn is_sensitive_field(field: &str) -> bool {
    let fl = field.to_lowercase();
    fl.contains("owner")
        || fl.contains("admin")
        || fl.contains("authority")
        || fl.contains("manager")
        || fl.contains("controller")
        || fl.contains("paused")
        || fl.contains("frozen")
        || fl.contains("config")
        || fl.contains("operator")
}

/// Returns the tokenized-source form of the recognized caller/access-control
/// checks the detector treats as sufficient. Reused for both the message body
/// and for resolved guard-helper bodies.
fn body_contains_caller_check(body: &str) -> bool {
    body.contains("caller")
        || body.contains("ensure !")
        || body.contains("ensure!")
        || body.contains("assert !")
        || body.contains("assert!")
        || body.contains("only_owner")
        || body.contains("authorize")
        || (body.contains("owner") && (body.contains("== ") || body.contains("!= ")))
        || (body.contains("admin") && (body.contains("== ") || body.contains("!= ")))
}

/// Recursively determine whether a called same-file helper (or a helper it
/// itself calls) performs a caller check. Bounded depth + visited set prevent
/// cycles. Unresolvable names simply return false (never assumed safe).
fn resolved_call_has_check(
    bodies: &HashMap<String, String>,
    name: &str,
    visited: &mut Vec<String>,
    depth: usize,
) -> bool {
    const MAX_DEPTH: usize = 4;
    if depth >= MAX_DEPTH {
        return false;
    }
    if visited.iter().any(|v| v == name) {
        return false;
    }
    let body = match bodies.get(name) {
        Some(b) => b,
        None => return false,
    };
    if body_contains_caller_check(body) {
        return true;
    }
    visited.push(name.to_string());
    for callee in extract_self_method_calls(body) {
        if resolved_call_has_check(bodies, &callee, visited, depth + 1) {
            return true;
        }
    }
    false
}

/// Length of the leading assignment operator in `s`, if any. Recognizes plain
/// `=` (but not `==` or `=>`) and compound assignments (`+=`, `-=`, `*=`, `/=`,
/// `%=`, `&=`, `|=`, `^=`, `<<=`, `>>=`). Comparison operators return None.
fn assign_op_len(s: &str) -> Option<usize> {
    for op in ["<<=", ">>="] {
        if s.starts_with(op) {
            return Some(op.len());
        }
    }
    for op in ["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^="] {
        if s.starts_with(op) {
            return Some(op.len());
        }
    }
    if let Some(rest) = s.strip_prefix('=') {
        match rest.chars().next() {
            // `==` (comparison) or `=>` (match arm) — not an assignment.
            Some('=') | Some('>') => return None,
            _ => return Some(1),
        }
    }
    None
}

/// Given a body slice starting immediately after a `self .` occurrence, decide
/// whether it is an assignment to a self place. Parses the full place path
/// (`field`, `.field`, `[index]` chains) and only accepts it when the token
/// right after the place is an assignment operator. Returns
/// `(first_field_name, rhs_expression)`.
fn parse_self_assignment(after_self: &str) -> Option<(String, String)> {
    let s = after_self.trim_start();
    let first_end = s.find(|c: char| !c.is_alphanumeric() && c != '_')?;
    if first_end == 0 {
        return None;
    }
    let first_field = s[..first_end].to_string();
    let mut rest = &s[first_end..];

    loop {
        let t = rest.trim_start();
        if let Some(after_dot) = t.strip_prefix('.') {
            // Field access continuation: `. ident` (but not a method call).
            let ad = after_dot.trim_start();
            let id_end = ad
                .find(|c: char| !c.is_alphanumeric() && c != '_')
                .unwrap_or(ad.len());
            if id_end == 0 {
                return None;
            }
            let after_id = ad[id_end..].trim_start();
            if after_id.starts_with('(') {
                // `self.field.method(...)` — a method call, not an assignment.
                return None;
            }
            rest = &ad[id_end..];
            continue;
        } else if t.starts_with('[') {
            // Index continuation: skip a balanced `[ ... ]`.
            let bytes = t.as_bytes();
            let mut depth = 0usize;
            let mut end = None;
            for (idx, &b) in bytes.iter().enumerate() {
                match b {
                    b'[' => depth += 1,
                    b']' => {
                        depth -= 1;
                        if depth == 0 {
                            end = Some(idx);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            let end = end?;
            rest = &t[end + 1..];
            continue;
        } else if let Some(op_len) = assign_op_len(t) {
            let rhs_start = &t[op_len..];
            let rhs_end = rhs_start.find(';').unwrap_or(rhs_start.len());
            let rhs = rhs_start[..rhs_end].trim().to_string();
            return Some((first_field, rhs));
        } else {
            return None;
        }
    }
}

/// Extract all `self.<place> = <rhs>` writes from a tokenized body as
/// `(first_field_name, rhs_text)` pairs. Right-hand-side reads of `self.x`,
/// comparisons and match arms are excluded.
fn self_field_writes(body: &str) -> Vec<(String, String)> {
    let mut writes = Vec::new();
    let pat = "self .";
    let mut start = 0;
    while let Some(rel) = body[start..].find(pat) {
        let i = start + rel;
        // Skip when `self.` is the RHS of a binding/assignment (`let x = self.y`,
        // or the second `self` in `self.a = self.b`).
        let prefix = body[..i].trim_end();
        let is_rhs = prefix.ends_with("let") || prefix.ends_with('=');
        if !is_rhs {
            if let Some((field, rhs)) = parse_self_assignment(&body[i + pat.len()..]) {
                writes.push((field, rhs));
            }
        }
        start = i + pat.len();
    }
    writes
}

/// True when there is at least one write and every write stores an
/// environment-derived value the caller cannot control, and no written field is
/// sensitive.
fn all_writes_env_derived(writes: &[(String, String)]) -> bool {
    !writes.is_empty()
        && writes.iter().all(|(field, rhs)| {
            !is_sensitive_field(field)
                && (rhs.contains("block_timestamp") || rhs.contains("block_number"))
        })
}

/// Extract names of same-receiver method calls `self.<ident>(...)` from a body.
fn extract_self_method_calls(body: &str) -> Vec<String> {
    let mut calls = Vec::new();
    let pat = "self .";
    let mut start = 0;
    while let Some(rel) = body[start..].find(pat) {
        let i = start + rel;
        let rest = body[i + pat.len()..].trim_start();
        let ident_end = rest
            .find(|c: char| !c.is_alphanumeric() && c != '_')
            .unwrap_or(rest.len());
        if ident_end > 0 {
            let ident = &rest[..ident_end];
            let after = rest[ident_end..].trim_start();
            if after.starts_with('(') {
                let name = ident.to_string();
                if !calls.contains(&name) {
                    calls.push(name);
                }
            }
        }
        start = i + pat.len();
    }
    calls
}

/// Byte offset of the first `self.<place> = ...` write in the body, if any.
fn first_self_assign_offset(body: &str) -> Option<usize> {
    let pat = "self .";
    let mut start = 0;
    while let Some(rel) = body[start..].find(pat) {
        let i = start + rel;
        let prefix = body[..i].trim_end();
        let is_rhs = prefix.ends_with("let") || prefix.ends_with('=');
        if !is_rhs && parse_self_assignment(&body[i + pat.len()..]).is_some() {
            return Some(i);
        }
        start = i + pat.len();
    }
    None
}

/// True when the body contains a conditional early-return guard
/// (`if ... { return Err(..) }` / `return ;`) positioned before the first
/// storage write — the early-return equivalent of an assert!/ensure! guard.
fn has_early_return_guard(body: &str) -> bool {
    let off = first_self_assign_offset(body).unwrap_or(body.len());
    let pre = &body[..off];
    (pre.contains("return Err") || pre.contains("return ;")) && pre.contains("if ")
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
        MissingCallerCheckDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_missing_caller() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn set_value(&mut self, value: u32) {
                    self.value = value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing caller check");
    }

    #[test]
    fn test_no_finding_readonly_method() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn get_value(&self) -> u32 {
                    let x = self.value;
                    x
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag read-only &self methods"
        );
    }

    #[test]
    fn test_no_finding_with_caller_check() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn set_value(&mut self, value: u32) {
                    assert_eq!(self.env().caller(), self.owner);
                    self.value = value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag with caller check");
    }

    #[test]
    fn test_critical_for_owner_write() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn set_owner(&mut self, new_owner: AccountId) {
                    self.owner = new_owner;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect missing caller check on owner write"
        );
        assert_eq!(findings[0].severity, Severity::Critical);
    }

    #[test]
    fn test_reduced_severity_for_general_write() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn set_value(&mut self, value: u32) {
                    self.value = value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty(), "Should detect missing caller check");
        assert_eq!(findings[0].severity, Severity::High);
    }

    #[test]
    fn test_low_confidence_for_payable() {
        let source = r#"
            impl MyContract {
                #[ink(message, payable)]
                pub fn deposit(&mut self) {
                    self.balance = 100;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(!findings.is_empty());
        assert_eq!(findings[0].confidence, Confidence::Low);
    }

    #[test]
    fn test_no_finding_for_flip() {
        let source = r#"
            impl Flipper {
                #[ink(message)]
                pub fn flip(&mut self) {
                    self.value = !self.value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag known permissionless patterns like flip"
        );
    }

    #[test]
    fn test_no_finding_for_standard_transfer() {
        let source = r#"
            impl Erc20 {
                #[ink(message)]
                pub fn transfer(&mut self, to: AccountId, value: Balance) {
                    self.balances = value;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag PSP22/ERC20 standard transfer method"
        );
    }

    // FP idx 0: access control delegated to a private guard helper.
    #[test]
    fn test_no_finding_guard_helper() {
        let source = r#"
            impl MyContract {
                fn ensure_admin(&self) -> Result<(), Error> {
                    if self.env().caller() != self.admin {
                        return Err(Error::NotAdmin);
                    }
                    Ok(())
                }

                #[ink(message)]
                pub fn set_fee(&mut self, fee: u32) -> Result<(), Error> {
                    self.ensure_admin()?;
                    self.fee = fee;
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag when access control is delegated to a resolved guard helper"
        );
    }

    // Ensure the helper resolution does NOT silence a genuinely unguarded call:
    // a helper that performs no caller check must not suppress the finding.
    #[test]
    fn test_still_fires_helper_without_check() {
        let source = r#"
            impl MyContract {
                fn recompute(&self) -> u32 {
                    self.base * 2
                }

                #[ink(message)]
                pub fn set_fee(&mut self, fee: u32) -> Result<(), Error> {
                    let _ = self.recompute();
                    self.fee = fee;
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A helper that performs no caller check must not suppress the finding"
        );
    }

    // FP idx 1: OpenBrush-style attribute modifier.
    #[test]
    fn test_no_finding_openbrush_modifier() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                #[modifiers(only_owner)]
                pub fn set_fee(&mut self, fee: u32) -> Result<(), OwnableError> {
                    self.fee = fee;
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag methods guarded by an access-control attribute modifier"
        );
    }

    // FP idx 2: match-arm `=>` must not be mistaken for a storage write.
    #[test]
    fn test_no_finding_match_arm_no_write() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn quote(&mut self, amount: u128) -> u128 {
                    match self.mode {
                        Mode::Fixed => amount,
                        Mode::Scaled => amount * 2,
                    }
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "A read-only &mut self method (match arms, no assignment) should not be flagged"
        );
    }

    // FP idx 3: permissionless keeper writing only env-derived values.
    #[test]
    fn test_no_finding_env_derived_keeper() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn sync(&mut self) {
                    self.last_synced = self.env().block_timestamp();
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Writes of only env-derived values the caller cannot control should not be flagged"
        );
    }

    // A keeper method that ALSO stores a caller-controlled value must still fire.
    #[test]
    fn test_still_fires_keeper_with_controlled_write() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn sync(&mut self, rate: u128) {
                    self.last_synced = self.env().block_timestamp();
                    self.rate = rate;
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A caller-controlled write alongside an env write must still be flagged"
        );
    }

    // FP idx 4: state/deadline transition guarded by an early return.
    #[test]
    fn test_no_finding_early_return_guard() {
        let source = r#"
            impl Auction {
                #[ink(message)]
                pub fn finalize(&mut self) -> Result<(), Error> {
                    if self.env().block_timestamp() < self.deadline {
                        return Err(Error::TooEarly);
                    }
                    self.finalized = true;
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Non-sensitive transition guarded by an early return should not be flagged"
        );
    }

    // The early-return relaxation must NOT hide a sensitive (owner/admin) write.
    #[test]
    fn test_still_fires_sensitive_write_with_early_return() {
        let source = r#"
            impl MyContract {
                #[ink(message)]
                pub fn rotate_admin(&mut self, new_admin: AccountId) -> Result<(), Error> {
                    if self.count > 10 {
                        return Err(Error::TooMany);
                    }
                    self.admin = new_admin;
                    Ok(())
                }
            }
        "#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "A sensitive admin write must still be flagged despite an unrelated early return"
        );
        assert_eq!(findings[0].severity, Severity::Critical);
    }
}
