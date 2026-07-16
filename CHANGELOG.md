# Changelog

All notable changes to RustDefend will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/), and this project adheres to [Semantic Versioning](https://semver.org/).

## [0.5.2] - 2026-07-15

Detector precision work (ADV-206) plus the false-negative regressions it introduced (ADV-233), released together. The FP reduction was never published on its own: v0.5.1 was tagged from `2b7d5ff`, which predates it.

### Fixed

- Restore detection in 26 detectors that the ADV-206 false-positive guards had silenced on genuinely vulnerable code (ADV-233)
- Guards now key on what code *does*, not what it is *named* or *spelled*. `fn_lower.contains("validate")` treated a helper named `validate_pda_seeds` as a signer check; `body_src.contains("is_signer")` treated a mere mention as a check; `body_has_bound_vocab` treated `v.len().checked_sub(1)` as a bounds check. All replaced with AST-structural analysis (ADV-233)
- Evaluate `#[cfg(..)]` predicates structurally instead of substring-matching their rendered tokens. `#[cfg(not(test))]` stringifies to `cfg (not (test))`, which contains `"test"` — production-only code was being skipped *as test code*. Affected INK-001, INK-004, NEAR-004, NEAR-005, CW-013 (ADV-233)
- Reduce false positives across all 61 detectors: 253 empirically-proven FPs eliminated with AST-based guards (ADV-206)
- Recognize validation delegated to a helper by resolving the callee body via the in-file call graph, not name-based skips (ADV-206)
- Match parsed tokens instead of raw source so patterns in comments and string literals no longer trigger findings (ADV-206)
- Skip `#[cfg(test)]` modules and test/mock helpers so non-shipped code is not flagged (ADV-206)
- Recognize const/literal and floating-point arithmetic operands to avoid spurious integer-overflow findings (ADV-206)
- `test_corpus_repos` cloned corpora into a path containing `integration_tests`, which the scanner skips as a test-path filter — suppressing ~80% of findings and failing CI for ~4 months (ADV-228)

### Changed

- Add a must-still-flag regression test per fixed detector, asserting the detector still reports the vulnerability it exists for. The suite was previously ~388 should-not-flag vs ~111 must-still-flag, so a guard that silenced a detector entirely passed CI — which is how ADV-206 regressed 26 detectors with 570 green tests. Suite now 661 tests, 0 failures (ADV-233, ADV-235)
- Pin integration corpora to exact commits and tighten expected ranges; the old bounds were wide enough to stay green through a catastrophic recall loss (ADV-228)

## [0.5.0] - 2026-02-17

### Added

- **5 new Solana detectors** (61 total, Solana: 21):
  - SOL-017: Account data matching — detects account data deserialization without field validation (High/Medium)
  - SOL-018: Unsafe account reallocation — detects `.realloc()` without signer and rent checks (High/Medium)
  - SOL-019: Duplicate mutable accounts — detects multiple mutable AccountInfo params without key uniqueness assertion (High/Medium)
  - SOL-020: Checked arithmetic unwrap — detects `.checked_add().unwrap()` chains that panic instead of error propagation (Medium/High)
  - SOL-021: Unvalidated sysvar — detects sysvar params typed as AccountInfo without validation (Medium/Medium)
- **Custom rules engine** — define pattern-matching rules in `.rustdefend-rules.toml` without recompiling. `--rules <path>` flag to load custom detectors at runtime
- **Cross-file call graph analysis** — `--cross-file` flag extends intra-file call graph to crate-level, tracking function calls across file boundaries for more accurate false positive reduction
- **MIR analysis foundation** (proof of concept) — AST-level type inference extracts type annotations from variable declarations and `use` statements. `--type-aware` flag enables skipping arithmetic on known safe types (Uint128, U256, Decimal, etc.)
- **VS Code extension scaffold** — `vscode-extension/` directory with TypeScript extension that spawns `rustdefend scan --format sarif`, parses output, and creates VS Code diagnostic markers
- **Web dashboard scaffold** — `dashboard/` directory with static HTML/CSS/JS app for loading and viewing RustDefend JSON reports with sortable/filterable table and expandable detail rows
- **crates.io publishing metadata** — repository, homepage, readme, keywords, categories, authors, exclude fields added to Cargo.toml
- **Community submission docs** — `docs/awesome-list-submission.md` with formatted descriptions for awesome-rust, awesome-solana-security, awesome-cosmwasm

### Changed

- Detector count: 56 → 61
- Solana detector count: 16 → 21

## [0.4.0] - 2026-02-17

### Added

- **Workspace-aware chain detection** — monorepo support: reads workspace member Cargo.tomls to map each crate to its specific chains, eliminating cross-chain noise (SOL detectors no longer fire on NEAR/CosmWasm code in the same workspace)
- **Intra-file call graph analysis** — builds per-file call graph from AST. Before emitting findings, checks if any caller already performs the relevant security check (signer, owner, input validation). Reduces false positives for helper functions called from checked entry points
- **Baseline diff for CI** — `--save-baseline <path.json>` captures current findings; `--baseline <path.json>` shows only new findings. Fingerprints are line-number-independent (stable across code insertions)
- **Project config** — `.rustdefend.toml` support with `ignore` (detector IDs), `ignore_files` (glob patterns), `min_severity`, `min_confidence`
- **Incremental scan caching** — `--incremental` flag caches findings per file keyed by mtime. Unchanged files skip read/parse/detect entirely. Cache stored at `--cache-path` or `<scan_root>/.rustdefend.cache.json`
- **6 new detectors** (56 total):
  - SOL-015: Lookup table manipulation — detects `AddressLookupTableAccount` usage without authority/freeze verification (High/Medium)
  - SOL-016: Missing priority fee — detects `set_compute_unit_limit` without `set_compute_unit_price` (Low/Low)
  - CW-012: Sylvia pattern issues — detects `#[sv::msg(exec)]` methods without auth checks (Medium/Medium)
  - CW-013: CW2 migration issues — detects cosmwasm-std 2.x API misuse (`from_binary`/`to_binary` deprecated) (Medium/Medium)
  - DEP-003: Build script abuse — detects `build.rs` with network downloads or shell execution (Critical/Medium)
  - DEP-004: Proc-macro supply chain — detects proc-macro deps with unpinned versions (High/Low)
- **Integration test corpus** — automated validation against 3 real-world repos (solana-attack-vectors, cosmwasm-security-dojo, scout-audit), gated behind `--features integration-tests`
- **Criterion benchmarks** — `cargo bench` measures scan throughput for single file, directory, and test fixtures

## [0.3.2] - 2026-02-17

### Changed

- **36% false positive reduction** validated against 6 real-world repositories (SPL, Anchor, Neodyme CTF, CW-Plus, CosmWasm CTF, NEAR SDK) — 820 → 521 findings
- Real-world corpus baseline added to GROUND_TRUTH_BASELINE.md with per-repo finding counts and TP estimates

### Fixed

- **SOL-003** FP reduction: Require Solana-specific source markers (eliminates cross-chain noise on CW/NEAR repos). Skip math helper functions (`calculate_*`, `compute_*`, `*_fee`, `*_rate`). Skip functions with assert/require bounds checks. Skip SPL library paths
- **SOL-001** FP reduction: Skip `process_*` sub-handlers dispatched from signer-checking entry points. Skip CPI wrapper helpers (`transfer`, `burn`, `mint_to`, `freeze`, `thaw`, etc.) and naming patterns (`*_tokens`, `*_account`). Skip SPL/Anchor library paths
- **SOL-012** FP reduction: Added Anchor repo-structure path exclusions (`/anchor/spl/`, `/anchor/lang/`, `/codegen/`)
- **INK-002** FP reduction: Require ink!-specific source markers (`#[ink(`, `ink_storage`, `ink_env`). Eliminates all cross-chain FPs
- **CW-001** FP reduction: Skip test/mock file paths (`/testing/`, `integration_tests/`, `multitest/`)
- **NEAR-010** FP reduction: Skip NEP standard methods (`ft_transfer`, `nft_mint`, `storage_deposit`, etc.)
- Updated test fixtures for SOL-001 and INK-002 to match new FP filters

## [0.3.1] - 2026-02-17

### Added

- **Vulnerability name in findings** — all output formats (text, JSON, SARIF) now show the detector name as a title (e.g. "Missing Owner Check") alongside the detector ID
- 8 new FP-specific unit tests across 6 detectors (139 total tests)

### Changed

- **CW-001** (integer overflow): Downgraded from Medium/Medium to **Low/Low** — Uint128/Uint256 panics are safe reverts, not exploitable. Skips test/mock/helper functions
- **CW-002** (reentrancy): Now only flags IBC handlers, reply handlers, and SubMsg dispatchers — CosmWasm is non-reentrant by design. Non-IBC execute handlers no longer flagged

### Fixed

- **SOL-001** FP reduction: Skip internal helpers (`_*`, `inner_*`, `do_*`, `handle_*`), utility functions (`validate*`, `serialize*`, `parse*`), expanded non-signer param exclusions
- **SOL-010** FP reduction: Skip Anchor codegen files and functions, recognize intentionally global PDAs (`b"config"`, `b"state"`, `b"vault"`, etc.)
- **INK-003** FP reduction: Skip known permissionless patterns (`flip`, `increment`, `vote`), PSP22/PSP34 standard methods (`transfer`, `approve`)
- **CW-009** FP reduction: Skip mock/helper/setup functions and test-related file paths
- Updated test fixtures for SOL-010 and CW-002 to match new FP filters

## [0.3.0] - 2026-02-16

### Added

- **5 new detectors** for medium-priority coverage gaps (50 total)
  - CW-010: Unguarded migrate entry — detects migrate handler without admin/sender check or version validation
  - CW-011: Missing reply ID validation — detects reply handler not matching on msg.id
  - NEAR-011: Unguarded storage unregister — detects storage_unregister without balance/force checks
  - NEAR-012: Missing gas for callbacks — detects cross-contract calls without explicit gas specification
  - INK-011: Unguarded set_code_hash — detects set_code_hash usage without admin/owner verification
- Test fixtures for all 5 new detectors

## [0.2.0] - 2026-02-16

### Added

- **5 new detectors** for actively exploited 2024+ vulnerability classes (45 total)
  - SOL-012: Token-2022 extension safety — detects programs accepting Token-2022 tokens without checking for dangerous extensions (PermanentDelegate, TransferHook, MintCloseAuthority)
  - SOL-013: Unsafe remaining_accounts — detects ctx.remaining_accounts usage without owner/type/key validation
  - SOL-014: init_if_needed reinitialization — detects Anchor init_if_needed without guard checks
  - CW-008: Unsafe IBC entry points — detects IBC packet handlers without channel validation or timeout rollback
  - DEP-002: Supply chain risk indicators — detects wildcard versions, unpinned git deps, and known-malicious crate names
- Test fixtures for all 5 new detectors
- Known malicious crate name database (10 crates from 2024-2025 supply chain attacks)

## [0.1.0] - 2026-02-13

### Added

- **40 detectors** across 4 chains + cross-chain dependency analysis
  - Solana (11): SOL-001 through SOL-011
  - CosmWasm (8): CW-001 through CW-007, CW-009
  - NEAR (10): NEAR-001 through NEAR-010
  - ink! (10): INK-001 through INK-010
  - Cross-chain (1): DEP-001
- AST-based analysis via `syn` crate (no regex)
- Auto-detects chain from `Cargo.toml` dependencies
- Parallel file processing via `rayon`
- Output formats: text (colored), JSON, SARIF v2.1.0
- Inline suppression: `// rustdefend-ignore` and `// rustdefend-ignore[SOL-001]`
- Severity and confidence filtering
- Per-detector filtering by ID
- Quiet mode for CI/CD (exit code only)

### Changed

- **Severity calibration** for 2024+ ecosystem mitigations:
  - CW-001 (integer overflow): Critical -> Low (CosmWasm Uint128/256 panics on overflow)
  - CW-002 (reentrancy): Medium -> Low (CosmWasm actor model is non-reentrant by design, only IBC/reply flagged)
  - INK-002 (integer overflow): Critical -> Low (`cargo-contract` enables overflow-checks by default)
  - SOL-009 (CPI reentrancy): Confidence Medium -> Low (Solana account locking mitigates)

### Fixed

- SOL-003 false positive filters: skip literals, string concatenation, widening casts, `checked_*`/`saturating_*`/`wrapping_*`, pack/serialization functions
- INK-003 risk stratification: Critical for sensitive fields, High for general writes, Medium/Low for permissionless patterns
