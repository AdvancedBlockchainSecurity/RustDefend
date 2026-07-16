# RustDefend

[![Crates.io](https://img.shields.io/crates/v/rustdefend)](https://crates.io/crates/rustdefend)
[![CI](https://github.com/AdvancedBlockchainSecurity/RustDefend/actions/workflows/ci.yml/badge.svg)](https://github.com/AdvancedBlockchainSecurity/RustDefend/actions)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

Static security scanner for Rust smart contracts. Analyzes source code via AST parsing (`syn` crate) to detect vulnerabilities across Solana, CosmWasm, NEAR, and ink! ecosystems.

- **61 detectors** covering the most common smart contract vulnerability classes
- **AST-based analysis** — parses Rust source into syntax trees, no regex pattern matching
- **Intra-file call graph** — tracks function calls to avoid flagging helpers called from checked entry points
- **Workspace-aware** — detects chains per-crate in monorepos, eliminating cross-chain noise
- **Auto-detects chain** from `Cargo.toml` dependencies (solana-program, cosmwasm-std, near-sdk, ink)
- **Baseline diff for CI** — track findings over time, show only new findings in pull requests
- **Incremental scanning** — caches results per file, skips unchanged files on re-scan
- **Project config** — `.rustdefend.toml` for ignoring detectors, files, and setting severity thresholds
- **Parallel file processing** via `rayon` for fast scans on large codebases
- **Multiple output formats** — colored text, JSON, SARIF v2.1.0
- **~65% true positive rate** validated against 6 real-world repositories (SPL, Anchor, cw-plus, NEAR SDK, Neodyme CTF, CosmWasm CTF)

## Installation

### From crates.io

```bash
cargo install rustdefend
```

### From source

Requires Rust 1.70+.

```bash
git clone https://github.com/AdvancedBlockchainSecurity/RustDefend.git
cd RustDefend
cargo install --path .
```

### Pre-built binaries

Download from [GitHub Releases](https://github.com/AdvancedBlockchainSecurity/RustDefend/releases). Available for Linux (x86_64, aarch64), macOS (x86_64, aarch64), and Windows (x86_64).

## Usage

```bash
# Scan a project (chain auto-detected from Cargo.toml)
rustdefend scan /path/to/project

# Force a specific chain
rustdefend scan /path/to/project --chain solana

# Filter by severity and confidence
rustdefend scan . --severity critical,high
rustdefend scan . --confidence high

# Run specific detectors
rustdefend scan . --detector SOL-001,SOL-003

# Output formats
rustdefend scan . --format text    # colored terminal output (default)
rustdefend scan . --format json    # JSON array
rustdefend scan . --format sarif   # SARIF v2.1.0 for CI/CD

# Baseline diff (CI workflows)
rustdefend scan . --save-baseline baseline.json    # capture current findings
rustdefend scan . --baseline baseline.json         # show only new findings

# Incremental scanning (skip unchanged files)
rustdefend scan . --incremental
rustdefend scan . --incremental --cache-path .rustdefend.cache.json

# Project config
rustdefend scan . --config .rustdefend.toml

# Custom rules (TOML-defined pattern matching)
rustdefend scan . --rules .rustdefend-rules.toml

# Cross-file call graph analysis
rustdefend scan . --cross-file

# Type-aware analysis (AST-level type inference)
rustdefend scan . --type-aware

# List available detectors
rustdefend list-detectors
rustdefend list-detectors --chain near

# Quiet mode (exit code only: 0=clean, 1=findings)
rustdefend scan . --quiet
```

## Project Config

Create a `.rustdefend.toml` in your project root:

```toml
# Detector IDs to ignore project-wide
ignore = ["SOL-003", "CW-001"]

# File patterns to skip entirely
ignore_files = ["generated/**", "vendor/**"]

# Optional minimum severity/confidence
min_severity = "high"
min_confidence = "medium"
```

Pass explicitly with `--config` or place at the project root for auto-detection.

## Detectors

61 detectors across 4 chains + cross-chain dependency analysis:

| Chain | Count | Docs |
|-------|-------|------|
| Solana | 21 | [docs/detectors/solana/](docs/detectors/solana/) |
| CosmWasm | 13 | [docs/detectors/cosmwasm/](docs/detectors/cosmwasm/) |
| NEAR | 12 | [docs/detectors/near/](docs/detectors/near/) |
| ink! | 11 | [docs/detectors/ink/](docs/detectors/ink/) |
| Cross-chain | 4 | [docs/detectors/common/](docs/detectors/common/) |

See [docs/detectors/](docs/detectors/) for the full detector index and [all_detectors.json](docs/detectors/all_detectors.json) for machine-readable metadata.

## CI/CD Integration

### GitHub Actions (SARIF)

```yaml
- name: Run RustDefend
  run: |
    rustdefend scan . --format sarif > results.sarif
  continue-on-error: true

- name: Upload SARIF
  uses: github/codeql-action/upload-sarif@v3
  with:
    sarif_file: results.sarif
```

### Baseline diff (block PRs on new findings only)

```yaml
- name: Run RustDefend (diff against baseline)
  run: |
    rustdefend scan . --baseline baseline.json --format json > new-findings.json
    COUNT=$(jq length new-findings.json)
    if [ "$COUNT" -gt 0 ]; then
      echo "$COUNT new findings detected"
      exit 1
    fi
```

### Exit codes

| Code | Meaning |
|------|---------|
| 0 | No findings |
| 1 | Findings detected |

## Inline Suppression

```rust
let total = amount + fee; // rustdefend-ignore
let total = amount + fee; // rustdefend-ignore[SOL-003]
```

- `rustdefend-ignore` suppresses all detectors for that line
- `rustdefend-ignore[ID]` suppresses a specific detector

## Changelog

See [CHANGELOG.md](CHANGELOG.md).

## License

MIT
