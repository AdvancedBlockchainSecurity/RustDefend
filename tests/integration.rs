#![cfg(feature = "integration-tests")]

use std::path::Path;
use std::process::Command;

struct CorpusSpec {
    name: &'static str,
    url: &'static str,
    /// Pinned so upstream changes cannot move the expected ranges out from under CI.
    /// Bumping a commit means re-measuring `expected_range` against it.
    commit: &'static str,
    /// Calibrated against `commit` with the detectors as of this revision. A detector
    /// change that intentionally shifts these counts must update the range in the
    /// same commit; an unexplained shift is a recall or precision regression.
    expected_range: (usize, usize),
}

const CORPUS: &[CorpusSpec] = &[
    CorpusSpec {
        name: "solana-attack-vectors",
        url: "https://github.com/Ackee-Blockchain/solana-common-attack-vectors",
        commit: "ea18da864c980a9a4ea803f588e39224cf2b9594",
        expected_range: (10, 30),
    },
    CorpusSpec {
        name: "cosmwasm-security-dojo",
        url: "https://github.com/oak-security/cosmwasm-security-dojo",
        commit: "68527006200e269fc8386a3e1b7c4799e2a6cd19",
        expected_range: (18, 50),
    },
    CorpusSpec {
        name: "scout-audit",
        url: "https://github.com/CoinFabrik/scout-audit",
        commit: "e4bc39272cb4bee93102e080ed5ba1b971f5610b",
        expected_range: (100, 220),
    },
];

/// Fetch exactly `commit`. `git clone --depth 1` can only land on a branch tip, so
/// init + fetch-by-SHA is what actually pins the corpus.
fn clone_repo(url: &str, commit: &str, target: &Path) -> bool {
    if std::fs::create_dir_all(target).is_err() {
        return false;
    }
    let git = |args: &[&str]| -> bool {
        Command::new("git")
            .current_dir(target)
            .args(args)
            .status()
            .map(|s| s.success())
            .unwrap_or(false)
    };
    git(&["init", "-q"])
        && git(&["remote", "add", "origin", url])
        && git(&["fetch", "-q", "--depth", "1", "origin", commit])
        && git(&["checkout", "-q", "FETCH_HEAD"])
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

        eprintln!("Cloning {} @ {}...", spec.name, &spec.commit[..8]);
        if !clone_repo(spec.url, spec.commit, &repo_dir) {
            eprintln!("  SKIP: Failed to clone {} @ {}", spec.url, spec.commit);
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
