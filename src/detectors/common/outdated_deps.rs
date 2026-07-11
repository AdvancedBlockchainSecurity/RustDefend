use std::path::PathBuf;

use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;

pub struct OutdatedDepsDetector;

impl Detector for OutdatedDepsDetector {
    fn id(&self) -> &'static str {
        "DEP-001"
    }
    fn name(&self) -> &'static str {
        "outdated-dependencies"
    }
    fn description(&self) -> &'static str {
        "Detects known-vulnerable dependency versions in Cargo.toml"
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
        // DEP-001 operates on Cargo.toml, not .rs files
        // Actual detection happens via detect_cargo_toml() called from Scanner
        Vec::new()
    }
}

struct VulnerableRange {
    crate_name: &'static str,
    description: &'static str,
    advisory: &'static str,
    // Versions that are vulnerable (simplified: major.minor.patch)
    is_vulnerable: fn(&str) -> bool,
    chain: Chain,
}

fn parse_version(v: &str) -> Option<(u32, u32, u32)> {
    let v = v
        .trim()
        .trim_start_matches('^')
        .trim_start_matches('~')
        .trim_start_matches('=');
    let parts: Vec<&str> = v.split('.').collect();
    let major = parts.first()?.parse().ok()?;
    let minor = parts.get(1).and_then(|p| p.parse().ok()).unwrap_or(0);
    let patch = parts.get(2).and_then(|p| p.parse().ok()).unwrap_or(0);
    Some((major, minor, patch))
}

fn version_lt(v: &str, target: (u32, u32, u32)) -> bool {
    if let Some((maj, min, pat)) = parse_version(v) {
        (maj, min, pat) < target
    } else {
        false
    }
}

fn version_in_range(v: &str, min: (u32, u32, u32), max_exclusive: (u32, u32, u32)) -> bool {
    if let Some(ver) = parse_version(v) {
        ver >= min && ver < max_exclusive
    } else {
        false
    }
}

const VULNERABLE_RANGES: &[VulnerableRange] = &[
    VulnerableRange {
        crate_name: "cosmwasm-std",
        description: "CWA-2024-002: Uint256::pow/Int256::neg use wrapping math",
        advisory: "CWA-2024-002 / CVE-2024-58263",
        is_vulnerable: |v| {
            version_lt(v, (1, 4, 4))
                || version_in_range(v, (1, 5, 0), (1, 5, 4))
                || version_in_range(v, (2, 0, 0), (2, 0, 2))
        },
        chain: Chain::CosmWasm,
    },
    VulnerableRange {
        crate_name: "cosmwasm-vm",
        description: "CWA-2025-001: VM memory safety issue",
        advisory: "CWA-2025-001",
        is_vulnerable: |v| version_lt(v, (1, 5, 8)) || version_in_range(v, (2, 0, 0), (2, 0, 6)),
        chain: Chain::CosmWasm,
    },
    VulnerableRange {
        crate_name: "near-sdk",
        description: "Legacy callback handling issues",
        advisory: "NEAR SDK < 4.0.0",
        is_vulnerable: |v| version_lt(v, (4, 0, 0)),
        chain: Chain::Near,
    },
    VulnerableRange {
        crate_name: "ink",
        description: "Pre-reentrancy-default versions lack safe defaults",
        advisory: "ink! < 4.0.0",
        is_vulnerable: |v| version_lt(v, (4, 0, 0)),
        chain: Chain::Ink,
    },
    VulnerableRange {
        crate_name: "anchor-lang",
        description: "Various account validation fixes",
        advisory: "Anchor < 0.28.0",
        is_vulnerable: |v| version_lt(v, (0, 28, 0)),
        chain: Chain::Solana,
    },
    VulnerableRange {
        crate_name: "solana-program",
        description: "Various runtime fixes",
        advisory: "solana-program < 1.16.0",
        is_vulnerable: |v| version_lt(v, (1, 16, 0)),
        chain: Chain::Solana,
    },
];

impl OutdatedDepsDetector {
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

        // Check [dependencies] and [dev-dependencies]
        for section in &["dependencies", "dev-dependencies"] {
            if let Some(deps) = parsed.get(section).and_then(|v| v.as_table()) {
                check_deps_table(deps, &content, cargo_toml_path, false, &mut findings);
            }
        }

        // Also check workspace dependencies
        if let Some(workspace) = parsed.get("workspace") {
            if let Some(deps) = workspace.get("dependencies").and_then(|v| v.as_table()) {
                check_deps_table(deps, &content, cargo_toml_path, true, &mut findings);
            }
        }

        findings
    }
}

/// Scan a dependency table, honoring Cargo's `package = "..."` rename so that the
/// crate identity we test against advisories is the *real* fetched crate, not the
/// local alias used as the table key.
///
/// - `ink = { version = "3.0", package = "inkjet" }` resolves to the unrelated
///   crate `inkjet`; the ink! framework is not in the graph, so it must NOT flag.
/// - Symmetrically, `myink = { version = "3.0", package = "ink" }` genuinely pulls
///   in `ink`, so it MUST still be checked (no false negative from key-only lookup).
fn check_deps_table(
    deps: &toml::value::Table,
    content: &str,
    cargo_toml_path: &PathBuf,
    is_workspace: bool,
    findings: &mut Vec<Finding>,
) {
    for (key, dep) in deps {
        // Resolve the version requirement and the *effective* crate name.
        let (version, effective_name) = match dep {
            toml::Value::String(v) => (v.clone(), key.as_str()),
            toml::Value::Table(t) => {
                if t.contains_key("git") || t.contains_key("path") {
                    continue; // Can't check git/path deps
                }
                // `package = "X"` renames the crate: the real dependency is X,
                // and `key` is only the local import alias.
                let effective = t
                    .get("package")
                    .and_then(|p| p.as_str())
                    .unwrap_or(key.as_str());
                let version = t
                    .get("version")
                    .and_then(|v| v.as_str())
                    .unwrap_or("")
                    .to_string();
                (version, effective)
            }
            _ => continue,
        };

        if version.is_empty() || version == "*" {
            continue;
        }

        for range in VULNERABLE_RANGES {
            if range.crate_name != effective_name {
                continue;
            }

            if (range.is_vulnerable)(&version) {
                // Anchor the reported line on the table key actually written in
                // the file (which may be a `package` alias).
                let line = find_dep_line(content, key);

                let message = if is_workspace {
                    format!(
                        "Vulnerable workspace dependency: {} = \"{}\" ({})",
                        range.crate_name, version, range.description
                    )
                } else {
                    format!(
                        "Vulnerable dependency: {} = \"{}\" ({})",
                        range.crate_name, version, range.description
                    )
                };

                findings.push(Finding {
                    detector_id: "DEP-001".to_string(),
                    name: "outdated-dependencies".to_string(),
                    severity: Severity::High,
                    confidence: Confidence::High,
                    message,
                    file: cargo_toml_path.clone(),
                    line,
                    column: 1,
                    snippet: format!("{} = \"{}\"", range.crate_name, version),
                    recommendation: format!(
                        "Update {} to a patched version. Advisory: {}",
                        range.crate_name, range.advisory
                    ),
                    chain: range.chain,
                });
            }
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
        let tmp = std::env::temp_dir().join(format!("rustdefend_test_cargo_{}.toml", id));
        let mut f = std::fs::File::create(&tmp).unwrap();
        f.write_all(cargo_toml.as_bytes()).unwrap();
        let results = OutdatedDepsDetector.detect_cargo_toml(&tmp);
        let _ = std::fs::remove_file(&tmp);
        results
    }

    #[test]
    fn test_detects_vulnerable_cosmwasm() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
cosmwasm-std = "1.4.0"
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            !findings.is_empty(),
            "Should detect vulnerable cosmwasm-std"
        );
        assert_eq!(findings[0].detector_id, "DEP-001");
    }

    #[test]
    fn test_no_finding_patched_version() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
cosmwasm-std = "2.1.0"
"#;
        let findings = run_detector(cargo_toml);
        assert!(findings.is_empty(), "Should not flag patched version");
    }

    #[test]
    fn test_detects_old_anchor() {
        let cargo_toml = r#"
[package]
name = "my-program"
version = "0.1.0"

[dependencies]
anchor-lang = "0.27.0"
"#;
        let findings = run_detector(cargo_toml);
        assert!(!findings.is_empty(), "Should detect old anchor-lang");
    }

    #[test]
    fn test_skips_git_deps() {
        let cargo_toml = r#"
[package]
name = "my-contract"
version = "0.1.0"

[dependencies]
cosmwasm-std = { git = "https://github.com/CosmWasm/cosmwasm", branch = "main" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(findings.is_empty(), "Should skip git dependencies");
    }

    // FP idx 3: a dependency renamed via `package = "..."` must be identified by
    // the real crate it fetches, not the local table-key alias. Here the key is
    // `ink` but the actual crate is the unrelated `inkjet`, so the "ink! < 4.0.0"
    // advisory cannot apply and no finding must be produced.
    #[test]
    fn test_no_finding_package_rename_to_unrelated_crate() {
        let cargo_toml = r#"
[package]
name = "my-crate"
version = "0.1.0"

[dependencies]
ink = { version = "3.0", package = "inkjet" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            findings.is_empty(),
            "Should not flag `ink` alias that actually resolves to the crate `inkjet`"
        );
    }

    // Symmetric true-positive guard for the same fix: a monitored crate pulled in
    // under a *different* alias via `package = "ink"` genuinely brings the
    // vulnerable ink! framework into the graph and MUST still be flagged. This
    // ensures honoring `package` did not introduce a false negative.
    #[test]
    fn test_detects_monitored_crate_under_alias() {
        let cargo_toml = r#"
[package]
name = "my-crate"
version = "0.1.0"

[dependencies]
my_ink = { version = "3.0", package = "ink" }
"#;
        let findings = run_detector(cargo_toml);
        assert!(
            !findings.is_empty(),
            "Should detect vulnerable `ink` even when aliased under another key"
        );
        assert_eq!(findings[0].chain, Chain::Ink);
    }
}
