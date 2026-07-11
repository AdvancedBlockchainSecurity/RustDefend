use std::path::PathBuf;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;

pub struct SupplyChainDetector;

impl Detector for SupplyChainDetector {
    fn id(&self) -> &'static str {
        "DEP-002"
    }
    fn name(&self) -> &'static str {
        "supply-chain-risk"
    }
    fn description(&self) -> &'static str {
        "Detects wildcard versions, unpinned git deps, and known-malicious crate names in Cargo.toml"
    }
    fn severity(&self) -> Severity {
        Severity::High
    }
    fn confidence(&self) -> Confidence {
        Confidence::High
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    } // Listed under Solana but applies cross-chain

    fn detect(&self, _ctx: &ScanContext) -> Vec<Finding> {
        // DEP-002 operates on Cargo.toml, not .rs files
        // Actual detection happens via detect_cargo_toml() called from Scanner
        Vec::new()
    }
}

const KNOWN_MALICIOUS_CRATES: &[&str] = &[
    "rustdecimal",
    "faster_log",
    "async_println",
    "finch-rust",
    "finch-rst",
    "sha-rust",
    "sha-rst",
    "finch_cli_rust",
    "polymarket-clients-sdk",
    "polymarket-client-sdks",
];

impl SupplyChainDetector {
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

        // Check [dependencies] for wildcards, unpinned git, and malicious crates
        if let Some(deps) = parsed.get("dependencies").and_then(|v| v.as_table()) {
            self.check_deps(&content, cargo_toml_path, deps, false, &mut findings);
        }

        // Check [dev-dependencies] - only for malicious crates and unpinned git
        // (crates.io allows wildcards in dev-dependencies)
        if let Some(deps) = parsed.get("dev-dependencies").and_then(|v| v.as_table()) {
            self.check_deps(&content, cargo_toml_path, deps, true, &mut findings);
        }

        // Check [workspace.dependencies]
        if let Some(workspace) = parsed.get("workspace") {
            if let Some(deps) = workspace.get("dependencies").and_then(|v| v.as_table()) {
                self.check_deps(&content, cargo_toml_path, deps, false, &mut findings);
            }
        }

        findings
    }

    fn check_deps(
        &self,
        content: &str,
        path: &PathBuf,
        deps: &toml::map::Map<String, toml::Value>,
        is_dev: bool,
        findings: &mut Vec<Finding>,
    ) {
        for (name, value) in deps {
            let line = find_dep_line(content, name);

            match value {
                toml::Value::String(version) => {
                    // For a bare string spec the map key IS the registry package name.
                    if KNOWN_MALICIOUS_CRATES.contains(&name.as_str()) {
                        self.push_malicious(path, line, name, findings);
                        continue;
                    }
                    // Skip dev-deps for wildcard detection
                    if !is_dev {
                        self.check_wildcard_version(content, path, name, version, line, findings);
                    }
                }
                toml::Value::Table(t) => {
                    // Skip path dependencies (local, not supply chain).
                    // A path dep is compiled from the local repository and is never
                    // fetched from crates.io, so a same-named registry crate is never
                    // downloaded. Perform this skip BEFORE the malicious-name check so a
                    // local utility crate that happens to share a listed name is exempt.
                    if t.contains_key("path") {
                        continue;
                    }

                    // Skip workspace = true (inherited spec). The real requirement lives
                    // in [workspace.dependencies], which is checked separately (either in
                    // this same file above, or when the workspace-root Cargo.toml is
                    // scanned). Skipping here avoids double-reporting an inherited spec and
                    // exempts local workspace crates that share a listed name.
                    if t.get("workspace").and_then(|v| v.as_bool()) == Some(true) {
                        continue;
                    }

                    // Resolve the effective registry package name. With `package = "..."`
                    // the map key is only a local alias used in `use` paths; the crate
                    // actually fetched is the one named by `package`. Matching the alias
                    // both false-positives on benign renames and false-negatives on
                    // malicious ones, so always resolve the real name first.
                    let effective = t
                        .get("package")
                        .and_then(|v| v.as_str())
                        .unwrap_or(name.as_str());
                    if KNOWN_MALICIOUS_CRATES.contains(&effective) {
                        self.push_malicious(path, line, effective, findings);
                        continue;
                    }

                    // Check git deps without rev or tag
                    if t.contains_key("git") {
                        let has_rev = t.contains_key("rev");
                        let has_tag = t.contains_key("tag");
                        if !has_rev && !has_tag {
                            findings.push(Finding {
                                detector_id: "DEP-002".to_string(),
                                name: "supply-chain-risk".to_string(),
                                severity: Severity::High,
                                confidence: Confidence::Medium,
                                message: format!(
                                    "Unpinned git dependency: '{}' has no rev or tag (mutable reference)",
                                    name
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
                                recommendation: format!(
                                    "Pin '{}' with rev = \"<commit-hash>\" or tag = \"<version>\" to prevent supply chain attacks via branch mutation",
                                    name
                                ),
                                chain: Chain::Solana,
                            });
                        }
                        continue;
                    }

                    // Check version field for wildcards (non-dev only)
                    if !is_dev {
                        if let Some(version) = t.get("version").and_then(|v| v.as_str()) {
                            self.check_wildcard_version(
                                content,
                                path,
                                name,
                                &version.to_string(),
                                line,
                                findings,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn push_malicious(
        &self,
        path: &PathBuf,
        line: usize,
        crate_name: &str,
        findings: &mut Vec<Finding>,
    ) {
        findings.push(Finding {
            detector_id: "DEP-002".to_string(),
            name: "supply-chain-risk".to_string(),
            severity: Severity::High,
            confidence: Confidence::High,
            message: format!(
                "Known malicious crate detected: '{}' (typosquatting/supply chain attack)",
                crate_name
            ),
            file: path.clone(),
            line,
            column: 1,
            snippet: format!("{} = ...", crate_name),
            recommendation: format!(
                "Remove '{}' immediately. This is a known malicious crate used in supply chain attacks",
                crate_name
            ),
            chain: Chain::Solana,
        });
    }

    fn check_wildcard_version(
        &self,
        content: &str,
        path: &PathBuf,
        name: &str,
        version: &str,
        line: usize,
        findings: &mut Vec<Finding>,
    ) {
        // Bounded comparison ranges are NOT wildcards. A requirement that carries an
        // upper-bound comparator (`<` / `<=`), e.g. ">= 0.7, < 0.9" or
        // "> 0.10, <= 0.10.55", resolves to a closed version window chosen by the
        // author and cannot silently pull a brand-new major/minor release. Treat any
        // requirement containing an upper bound as bounded and skip it. Truly
        // unbounded requirements ("*", ">= 0", ">= 0.x" with no upper bound) contain
        // no `<` and remain flagged below.
        if version.contains('<') {
            return;
        }

        let is_wildcard = version == "*"
            || version.ends_with(".*")
            || version == ">= 0"
            || version == "> 0"
            || version.starts_with(">= 0.")
            || version.starts_with("> 0.");

        if !is_wildcard {
            return;
        }

        if is_bounded_major_wildcard(version) {
            // A `<major>.*` requirement with a nonzero major (e.g. "1.*") resolves to
            // exactly the same closed range as the bare-major caret idiom: "1.*" ==
            // "1" == ^1 == >=1.0.0, <2.0.0 — which this detector treats as safe and
            // which is also the finding's own recommended fix ("1.0"). It grants no
            // more exposure to a malicious release than the ubiquitous bare-major
            // idiom, so report it only as a low-severity pinning-style nit rather than
            // a supply-chain wildcard. (Bounded below 2.0.0; "0.*" and bare "*" stay
            // High.)
            let caret = &version[..version.len() - 2];
            findings.push(Finding {
                detector_id: "DEP-002".to_string(),
                name: "supply-chain-risk".to_string(),
                severity: Severity::Low,
                confidence: Confidence::Low,
                message: format!(
                    "Loose version pin for '{}': \"{}\" is equivalent to caret \"{}\" (>= {}.0.0, < {}.0.0); consider an explicit pin",
                    name,
                    version,
                    caret,
                    caret,
                    next_major(caret)
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
                recommendation: format!(
                    "Pin '{}' to an explicit version (e.g., \"{}.0\") for reproducible builds",
                    name, caret
                ),
                chain: Chain::Solana,
            });
            return;
        }

        findings.push(Finding {
            detector_id: "DEP-002".to_string(),
            name: "supply-chain-risk".to_string(),
            severity: Severity::High,
            confidence: Confidence::High,
            message: format!(
                "Wildcard version for '{}': \"{}\" allows any version including malicious releases",
                name, version
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
            recommendation: format!(
                "Pin '{}' to a specific version range (e.g., \"1.0\" or \"^1.2.3\")",
                name
            ),
            chain: Chain::Solana,
        });
    }
}

/// True for a `<major>.*` requirement whose major is a single nonzero integer
/// component (e.g. "1.*", "2.*", "10.*"). Such requirements resolve to the same
/// closed range as the bare-major caret idiom ("1" == ^1 == >=1.0.0, <2.0.0),
/// which the detector treats as safe. "0.*" (all 0.x, loose) and multi-component
/// forms like "1.2.*" are intentionally excluded so they keep their High rating.
fn is_bounded_major_wildcard(version: &str) -> bool {
    if let Some(prefix) = version.strip_suffix(".*") {
        // Must be a single pure-digit component (no interior dot) that is not all zeros.
        return !prefix.is_empty()
            && prefix.chars().all(|c| c.is_ascii_digit())
            && prefix.chars().any(|c| c != '0');
    }
    false
}

/// Given a nonzero integer string, return the next major as a string. Falls back
/// to the input on overflow/parse failure (callers only pass validated digits).
fn next_major(major: &str) -> String {
    match major.parse::<u64>() {
        Ok(n) => (n.saturating_add(1)).to_string(),
        Err(_) => major.to_string(),
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
        let tmp = std::env::temp_dir().join(format!("rustdefend_test_sc_{}.toml", id));
        let mut f = std::fs::File::create(&tmp).unwrap();
        f.write_all(cargo_toml.as_bytes()).unwrap();
        let results = SupplyChainDetector.detect_cargo_toml(&tmp);
        let _ = std::fs::remove_file(&tmp);
        results
    }

    #[test]
    fn test_detects_wildcard_version() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
some-crate = "*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "Should detect wildcard version");
        assert_eq!(findings[0].detector_id, "DEP-002");
        assert!(findings[0].message.contains("Wildcard"));
    }

    #[test]
    fn test_detects_known_malicious_crate() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
rustdecimal = "0.3.1"
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "Should detect malicious crate");
        assert!(findings[0].message.contains("malicious"));
    }

    #[test]
    fn test_detects_unpinned_git_dep() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my-lib = { git = "https://github.com/example/lib", branch = "main" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "Should detect unpinned git dep");
        assert!(findings[0].message.contains("Unpinned"));
    }

    #[test]
    fn test_no_finding_for_path_deps() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my-lib = { path = "../my-lib" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(findings.is_empty(), "Should not flag path dependencies");
    }

    #[test]
    fn test_no_finding_for_pinned_git() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
my-lib = { git = "https://github.com/example/lib", rev = "abc123" }
another = { git = "https://github.com/example/other", tag = "v1.0.0" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(findings.is_empty(), "Should not flag pinned git deps");
    }

    #[test]
    fn test_detects_partial_wildcard() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
some-crate = "1.*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "Should detect partial wildcard");
    }

    #[test]
    fn test_skips_dev_deps_wildcards() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dev-dependencies]
test-helper = "*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "Should skip wildcard in dev-dependencies"
        );
    }

    // ---- FP regression tests ----

    // FP idx 0: bounded comparison ranges (explicit upper bound) are not wildcards.
    #[test]
    fn test_no_finding_for_bounded_comparison_ranges() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
zerocopy = ">= 0.7, < 0.9"
openssl = "> 0.10, <= 0.10.55"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "Bounded comparison ranges with an upper bound must not be flagged as wildcards, got: {:?}",
            findings
        );
    }

    // FP idx 0 (companion): a truly unbounded lower-bound requirement still fires.
    #[test]
    fn test_unbounded_lower_bound_still_flagged() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
loose = ">= 0.1"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            !findings.is_empty(),
            "Unbounded '>= 0.x' requirement must still be flagged"
        );
        assert!(findings[0].message.contains("Wildcard"));
    }

    // FP idx 1: local path / workspace crate that shares a name on the malicious list.
    #[test]
    fn test_no_finding_for_local_crate_sharing_malicious_name() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
faster_log = { path = "../faster_log" }
sha-rust = { workspace = true }
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "Local path/workspace crates must not be flagged as malicious, got: {:?}",
            findings
        );
    }

    // FP idx 2: renamed dependency alias resolves to the real (benign) package name.
    #[test]
    fn test_no_finding_for_benign_rename_alias() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
rustdecimal = { package = "rust_decimal", version = "1.33" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "A `package = \"rust_decimal\"` rename must not be flagged as malicious, got: {:?}",
            findings
        );
    }

    // FP idx 2 (companion): a malicious crate hidden behind a benign alias IS caught.
    #[test]
    fn test_detects_malicious_crate_behind_alias() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
safe_alias = { package = "rustdecimal", version = "1.0" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            !findings.is_empty(),
            "A malicious crate renamed via `package` must still be detected"
        );
        assert!(findings[0].message.contains("malicious"));
        assert!(findings[0].message.contains("rustdecimal"));
    }

    // FP idx 3: `<major>.*` with a nonzero major is downgraded, not reported as a
    // High/High supply-chain wildcard (it still fires as a low-severity nit).
    #[test]
    fn test_major_wildcard_downgraded_not_supply_chain() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
serde = "1.*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "Should still report '1.*'");
        assert_eq!(
            findings[0].severity,
            Severity::Low,
            "'1.*' (== ^1) must be downgraded from a supply-chain wildcard"
        );
        assert_eq!(findings[0].confidence, Confidence::Low);
        assert!(
            !findings[0].message.contains("malicious releases"),
            "Downgraded finding must not claim it allows malicious releases"
        );
    }

    // FP idx 3 (companion): a broad `0.*` requirement remains a High wildcard.
    #[test]
    fn test_zero_major_wildcard_stays_high() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
loose = "0.*"
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "'0.*' must still be flagged");
        assert_eq!(findings[0].severity, Severity::High);
        assert!(findings[0].message.contains("Wildcard"));
    }
}
