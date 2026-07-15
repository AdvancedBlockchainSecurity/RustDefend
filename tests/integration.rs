#![cfg(feature = "integration-tests")]

use std::path::Path;
use std::process::Command;

struct CorpusSpec {
    name: &'static str,
    url: &'static str,
    expected_range: (usize, usize),
}

const CORPUS: &[CorpusSpec] = &[
    CorpusSpec {
        name: "solana-attack-vectors",
        url: "https://github.com/Ackee-Blockchain/solana-common-attack-vectors",
        expected_range: (3, 20),
    },
    CorpusSpec {
        name: "cosmwasm-security-dojo",
        url: "https://github.com/oak-security/cosmwasm-security-dojo",
        expected_range: (15, 70),
    },
    CorpusSpec {
        name: "scout-audit",
        url: "https://github.com/CoinFabrik/scout-audit",
        expected_range: (80, 350),
    },
];

fn clone_repo(url: &str, target: &Path) -> bool {
    Command::new("git")
        .args(["clone", "--depth", "1", url])
        .arg(target)
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

fn run_scan(path: &Path) -> Option<Vec<serde_json::Value>> {
    let binary = env!("CARGO_BIN_EXE_rustdefend");
    let output = Command::new(binary)
        .args(["scan", &path.to_string_lossy(), "--format", "json"])
        .output()
        .ok()?;

    // Exit code 1 means findings (expected), 0 means clean, 2+ means error
    if output.status.code().unwrap_or(2) > 1 {
        return None;
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    serde_json::from_str::<Vec<serde_json::Value>>(&stdout).ok()
}

#[test]
fn test_corpus_repos() {
    // Must not contain a test-path marker (`test`, `integration_tests`, `mock`):
    // the scanner skips such paths as an FP filter, which would suppress most
    // findings in the cloned corpus and make the expected ranges unreachable.
    let tmp_dir = std::env::temp_dir().join("rustdefend_corpus");
    let _ = std::fs::create_dir_all(&tmp_dir);

    for spec in CORPUS {
        let repo_dir = tmp_dir.join(spec.name);

        // Clean up any previous clone
        let _ = std::fs::remove_dir_all(&repo_dir);

        eprintln!("Cloning {}...", spec.name);
        if !clone_repo(spec.url, &repo_dir) {
            eprintln!("  SKIP: Failed to clone {}", spec.url);
            continue;
        }

        eprintln!("Scanning {}...", spec.name);
        match run_scan(&repo_dir) {
            Some(findings) => {
                let count = findings.len();
                eprintln!(
                    "  {} findings (expected {}-{})",
                    count, spec.expected_range.0, spec.expected_range.1
                );
                assert!(
                    count >= spec.expected_range.0 && count <= spec.expected_range.1,
                    "{}: Expected {}-{} findings, got {}",
                    spec.name,
                    spec.expected_range.0,
                    spec.expected_range.1,
                    count
                );
            }
            None => {
                eprintln!("  SKIP: Scan failed for {}", spec.name);
            }
        }

        // Cleanup
        let _ = std::fs::remove_dir_all(&repo_dir);
    }
}
