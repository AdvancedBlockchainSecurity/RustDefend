use std::path::PathBuf;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;

pub struct ProcMacroRiskDetector;

impl Detector for ProcMacroRiskDetector {
    fn id(&self) -> &'static str {
        "DEP-004"
    }
    fn name(&self) -> &'static str {
        "proc-macro-supply-chain"
    }
    fn description(&self) -> &'static str {
        "Detects proc-macro dependencies with unpinned versions in Cargo.toml"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::Low
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    } // Listed under Solana but applies cross-chain

    fn detect(&self, _ctx: &ScanContext) -> Vec<Finding> {
        // DEP-004 operates on Cargo.toml, not .rs files
        // Actual detection happens via detect_cargo_toml() called from Scanner
        Vec::new()
    }
}

fn is_proc_macro_name(name: &str) -> bool {
    // Well-known helper/support libraries whose names merely *mention* "proc-macro"
    // but which are ordinary rlib crates, NOT `proc-macro = true` compiler plugins.
    // They do not execute at compile time, so the finding message ("proc macros
    // execute at compile time") is factually wrong for them and their risk profile
    // is identical to any ordinary library dependency (e.g. serde), which the
    // detector deliberately does not flag. See DEP-004 FP idx 1.
    const SUPPORT_LIBS: &[&str] = &[
        "proc-macro2",
        "proc_macro2",
        "proc-macro-error",
        "proc_macro_error",
        "proc-macro-error-attr",
        "proc_macro_error_attr",
        "proc-macro-crate",
        "proc_macro_crate",
    ];
    if SUPPORT_LIBS.contains(&name) {
        return false;
    }

    name.ends_with("_derive")
        || name.ends_with("_macro")
        || name.ends_with("-derive")
        || name.ends_with("-macro")
        || name.contains("proc-macro")
        || name.contains("proc_macro")
}

fn is_unpinned_version(version: &str) -> bool {
    // A wildcard spec is genuinely unpinned: fully "*" or a partial wildcard such
    // as "1.*" / "1.2.*" resolves to an unbounded latest release at build time.
    //
    // NOTE: A bare major-only spec such as "1" is NOT treated as unpinned. In Cargo
    // semver "1" is exactly "^1" — the same floating caret range class as "1.0" or
    // "1.0.193", which the detector deliberately accepts (see
    // test_no_finding_for_semver_range). Both float and both are pinned in practice
    // by the committed Cargo.lock that contracts ship with, so flagging one caret
    // spec but not the other is an inconsistency, not a supply-chain signal.
    // See DEP-004 FP idx 0.
    version.contains('*')
}

impl ProcMacroRiskDetector {
    pub fn detect_cargo_toml(&self, cargo_toml_path: &PathBuf) -> Vec<Finding> {
        let content = match std::fs::read_to_string(cargo_toml_path) {
            Ok(c) => c,
            Err(_) => return vec![],
        };

        let parsed: toml::Value = match content.parse() {
            Ok(v) => v,
            Err(_) => return vec![],
        };

        let mut findings = Vec::new();

        // Check [dependencies] only (not dev-dependencies)
        if let Some(deps) = parsed.get("dependencies").and_then(|v| v.as_table()) {
            self.check_deps(&content, cargo_toml_path, deps, &mut findings);
        }

        findings
    }

    fn check_deps(
        &self,
        content: &str,
        path: &PathBuf,
        deps: &toml::map::Map<String, toml::Value>,
        findings: &mut Vec<Finding>,
    ) {
        for (name, value) in deps {
            // Classify by the crate that is actually compiled, not the dependency
            // key. With `package = "..."` the key is an arbitrary local alias, so
            // classifying on the key both produces false positives (macro-like
            // alias over a plain library) and false negatives (real proc macro
            // renamed to a neutral key). Consult the `package` field when present.
            // See DEP-004 FP idx 2.
            let classify_name: &str = match value {
                toml::Value::Table(t) => t.get("package").and_then(|v| v.as_str()).unwrap_or(name),
                _ => name,
            };

            if !is_proc_macro_name(classify_name) {
                continue;
            }

            let line = find_dep_line(content, name);

            match value {
                toml::Value::String(version) => {
                    if is_unpinned_version(version) {
                        findings.push(self.make_finding(
                            path,
                            name,
                            &format!("version \"{}\"", version),
                            line,
                            content,
                        ));
                    }
                }
                toml::Value::Table(t) => {
                    // Skip path dependencies
                    if t.contains_key("path") {
                        continue;
                    }

                    // Skip workspace = true
                    if t.get("workspace").and_then(|v| v.as_bool()) == Some(true) {
                        continue;
                    }

                    // Check git deps without rev or tag
                    if t.contains_key("git") {
                        let has_rev = t.contains_key("rev");
                        let has_tag = t.contains_key("tag");
                        if !has_rev && !has_tag {
                            findings.push(self.make_finding(
                                path,
                                name,
                                "git dependency without rev or tag",
                                line,
                                content,
                            ));
                        }
                        continue;
                    }

                    // Check version field
                    if let Some(version) = t.get("version").and_then(|v| v.as_str()) {
                        if is_unpinned_version(version) {
                            findings.push(self.make_finding(
                                path,
                                name,
                                &format!("version \"{}\"", version),
                                line,
                                content,
                            ));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn make_finding(
        &self,
        path: &PathBuf,
        name: &str,
        detail: &str,
        line: usize,
        content: &str,
    ) -> Finding {
        Finding {
            detector_id: "DEP-004".to_string(),
            name: "proc-macro-supply-chain".to_string(),
            severity: Severity::High,
            confidence: Confidence::Low,
            message: format!(
                "Unpinned proc-macro dependency: '{}' has {} (proc macros execute at compile time)",
                name, detail
            ),
            file: path.clone(),
            line,
            column: 1,
            snippet: content
                .lines()
                .nth(line.saturating_sub(1))
                .unwrap_or("")
                .trim()
                .to_string(),
            recommendation: "Pin proc-macro dependencies to exact versions (e.g., \"=1.2.3\") as proc macros execute at compile time with full system access".to_string(),
            chain: Chain::Solana,
        }
    }
}

fn find_dep_line(content: &str, crate_name: &str) -> usize {
    for (i, line) in content.lines().enumerate() {
        if line.trim_start().starts_with(crate_name) {
            return i + 1;
        }
    }
    1
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn run_detector(cargo_toml: &str) -> Vec<Finding> {
        use std::sync::atomic::{AtomicU64, Ordering};
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let id = COUNTER.fetch_add(1, Ordering::SeqCst);
        let tmp = std::env::temp_dir().join(format!("rustdefend_test_pm_{}.toml", id));
        let mut f = std::fs::File::create(&tmp).unwrap();
        f.write_all(cargo_toml.as_bytes()).unwrap();
        let results = ProcMacroRiskDetector.detect_cargo_toml(&tmp);
        let _ = std::fs::remove_file(&tmp);
        results
    }

    #[test]
    fn test_detects_wildcard_proc_macro() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my_derive = "*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            !findings.is_empty(),
            "Should detect wildcard proc-macro dep"
        );
        assert_eq!(findings[0].detector_id, "DEP-004");
        assert!(findings[0].message.contains("proc-macro"));
    }

    #[test]
    fn test_no_finding_for_pinned_proc_macro() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my_derive = "=1.2.3"
"#;
        let findings = run_detector(cargo_toml);
        assert!(findings.is_empty(), "Should not flag pinned proc-macro dep");
    }

    // DEP-004 FP idx 0: a bare major-only spec ("1") is caret-equivalent to
    // "1.0" / "1.0.193" (which test_no_finding_for_semver_range accepts) and is
    // pinned in practice by the committed Cargo.lock. It must NOT be flagged.
    // (Replaces the former test_detects_unpinned_major_only, which encoded this
    // very false positive as a true positive.)
    #[test]
    fn test_no_finding_for_major_only_caret() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
serde = { version = "1", features = ["derive"] }
serde_derive = "1"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "Should not flag caret-equivalent major-only version for proc-macro"
        );
    }

    // A partial wildcard ("1.*") is genuinely unpinned and must still fire.
    #[test]
    fn test_detects_partial_wildcard() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
serde_derive = "1.*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            !findings.is_empty(),
            "Should detect partial wildcard version for proc-macro"
        );
    }

    #[test]
    fn test_no_finding_for_semver_range() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
serde_derive = "1.0.193"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "Should not flag version with minor+patch"
        );
    }

    #[test]
    fn test_detects_git_without_rev() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my-derive = { git = "https://github.com/example/lib", branch = "main" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            !findings.is_empty(),
            "Should detect unpinned git proc-macro dep"
        );
    }

    #[test]
    fn test_skips_path_deps() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my_derive = { path = "../my_derive" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(findings.is_empty(), "Should skip path dependencies");
    }

    #[test]
    fn test_skips_workspace_deps() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my_derive = { workspace = true }
"#;
        let findings = run_detector(cargo_toml);
        assert!(findings.is_empty(), "Should skip workspace dependencies");
    }

    #[test]
    fn test_skips_non_proc_macro_deps() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
serde = "*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(findings.is_empty(), "Should not flag non-proc-macro crates");
    }

    #[test]
    fn test_detects_dash_macro_suffix() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my-macro = "*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "Should detect -macro suffix");
    }

    #[test]
    fn test_detects_proc_macro_in_name() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my-proc-macro-lib = "*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "Should detect proc-macro in name");
    }

    // DEP-004 FP idx 1: proc-macro2 / proc-macro-error / proc-macro-crate are
    // ordinary rlib support libraries, not `proc-macro = true` crates. They must
    // not be flagged even with a floating "1" spec.
    #[test]
    fn test_no_finding_for_proc_macro_support_libs() {
        let cargo_toml = r#"
[package]
name = "contract-macros-support"
version = "0.1.0"

[dependencies]
proc-macro2 = "1"
proc-macro-error = "1"
proc-macro-crate = "*"
proc-macro-error-attr = "*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "Should not flag proc-macro support libraries (proc-macro2/error/crate)"
        );
    }

    // DEP-004 FP idx 2: a macro-like alias over a plain library via `package`
    // must be classified by the real (compiled) crate name, not the key.
    #[test]
    fn test_no_finding_for_renamed_non_macro_package() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
state_macro = { package = "state-utils", version = "*" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "Should not flag a macro-like alias whose real package is a plain library"
        );
    }

    // Mirror of FP idx 2: a real proc macro renamed to a neutral key must still be
    // detected (closes the corresponding false negative from the same root cause).
    #[test]
    fn test_detects_renamed_real_proc_macro() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
helper = { package = "evil_derive", version = "*" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            !findings.is_empty(),
            "Should detect a real proc macro renamed to a neutral key"
        );
    }
}
