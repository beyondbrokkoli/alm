//! L2 harness legs (REBASE_PLAN.md §4): the frozen-oracle parity leg —
//! every corpus case the FRONT END refuses must fail with diagnostics
//! byte-identical to mirror_experimental's compiled binary @ 87aca4c —
//! plus the 449-file front sweep.
//!
//! Header scanning happens in Rust on purpose: `grep` treats
//! `nul_string.lua` (a raw NUL inside) as binary and silently drops it
//! from `-l` lists; the harness may not lose cases to that.
//!
//! Trace pokes: mirror's stderr carries `ALM_TRACE: slot 1 — build
//! failed` on the negative lane (its build-fail poke); the comparison
//! filters exactly those lines — the plan's "modulo trace pokes". The
//! trace layer itself lands at L11; alm has no pokes yet.
//!
//! Both sides run RELEASE binaries, like run.lua's lane: the depth
//! guard cases recurse ~10 frames per nesting level to the 1024 limit,
//! and a debug build's frames overflow an 8 MiB stack before the guard
//! can fire — in BOTH compilers (mirror debug aborts on
//! `parser_depth_rejected.lua` identically). That is a shared
//! debug-profile artifact, not a divergence; release frames fit and
//! the guard refuses at exactly the pinned depth.

mod common;

use alm::dump::render_ast;
use common::{cases_dir, collect_lua_files, is_front_refusal, parse_on_big_stack};
use std::path::{Path, PathBuf};
use std::process::Command;

fn mirror_bin() -> PathBuf {
    if let Ok(custom) = std::env::var("ALM_MIRROR_BIN") {
        return PathBuf::from(custom);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../mirror_experimental/target/release/alm")
}

fn alm_bin() -> PathBuf {
    if let Ok(custom) = std::env::var("ALM_BIN") {
        return PathBuf::from(custom);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/release/alm")
}

/// One negative case: its FLAGS words, read from the `--` header
/// grammar (run.lua `parse_pins` keys).
struct Case {
    path: std::path::PathBuf,
    flags: Vec<String>,
}

impl Case {
    fn name(&self) -> String {
        self.path.file_name().unwrap().to_string_lossy().to_string()
    }

    /// The subset of FLAGS the L2 surface owns; later layers' flags
    /// (`--exe`, `--module-root`) are not yet alm's to take.
    fn surface_flags(&self) -> Vec<String> {
        self.flags
            .iter()
            .filter(|f| f.starts_with("--index-base=") || f.starts_with("--for-limit="))
            .cloned()
            .collect()
    }
}

fn read_negative_cases(root: &Path) -> Vec<Case> {
    let mut cases = Vec::new();
    for entry in std::fs::read_dir(root).expect("corpus root readable") {
        let path = entry.expect("corpus entry").path();
        if path.extension().is_some_and(|e| e == "lua") {
            let text = std::fs::read_to_string(&path).expect("case readable");
            if text.lines().any(|l| l.starts_with("-- EXPECT_BUILD_FAIL:")) {
                let flags = text
                    .lines()
                    .find_map(|l| l.strip_prefix("-- FLAGS:"))
                    .map(|rest| rest.split_whitespace().map(str::to_string).collect())
                    .unwrap_or_default();
                cases.push(Case { path, flags });
            }
        }
    }
    cases.sort_by(|a, b| a.path.cmp(&b.path));
    cases
}

fn run(bin: &Path, args: &[String]) -> std::process::Output {
    // Run from mirror's repo root (run.lua's convention): the trace
    // mmap sidecar (`.alm_trace.bin`) materializes in the oracle's
    // tree, not in alm's working copy.
    let cwd = bin
        .parent()
        .and_then(|p| p.parent())
        .expect("binary two levels deep in its repo");
    Command::new(bin)
        .args(args)
        .current_dir(cwd)
        .output()
        .unwrap_or_else(|e| panic!("running {} failed: {e}", bin.display()))
}

/// mirror's stderr minus the trace poke lines (the one sanctioned
/// difference; REBASE_PLAN.md §3.3.1 "modulo trace pokes").
fn without_trace_pokes(stderr: &[u8]) -> String {
    let text = String::from_utf8_lossy(stderr).into_owned();
    text.lines()
        .filter(|l| !l.starts_with("ALM_TRACE:"))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n"
}

#[test]
fn front_end_parity_vs_mirror_binary() {
    let bin = mirror_bin();
    assert!(
        bin.is_file(),
        "mirror binary {} missing — rebuild the frozen oracle first: \
         (cd ../mirror_experimental && cargo build --release)",
        bin.display(),
    );
    let mine = alm_bin();
    assert!(
        mine.is_file(),
        "alm release binary {} missing — build it first: \
         cargo build --release (the parity lane is release-vs-release; \
         see the module comment for why debug cannot carry the depth \
         guard cases)",
        mine.display(),
    );
    let cases = read_negative_cases(&cases_dir());
    assert!(
        cases.len() >= 120,
        "negative-case inventory shrank to {}",
        cases.len()
    );
    assert!(
        cases.iter().any(|c| c.name() == "nul_string.lua"),
        "nul_string.lua lost from the negative inventory — the harness \
         must read binary-content cases (grep -l drops them)"
    );

    let mut checked = 0;
    for case in &cases {
        let name = case.name();
        let mut mirror_args = case.flags.clone();
        mirror_args.push(case.path.display().to_string());
        let mirror = run(&bin, &mirror_args);

        if is_front_refusal(&name) {
            checked += 1;
            assert!(
                !mirror.status.success(),
                "{name}: mirror must fail the build (front refusal)"
            );
            let mirror_stderr = without_trace_pokes(&mirror.stderr);
            assert!(
                !mirror_stderr.contains("panicked at"),
                "{name}: mirror ICE'd"
            );

            let mut alm_args = case.surface_flags();
            alm_args.push(case.path.display().to_string());
            let alm = run(&mine, &alm_args);
            assert_eq!(
                Some(1),
                alm.status.code(),
                "{name}: alm front refusal must exit 1"
            );
            assert!(
                alm.stdout.is_empty(),
                "{name}: alm printed to stdout on a refusal"
            );
            let alm_stderr = String::from_utf8_lossy(&alm.stderr).into_owned();
            assert_eq!(
                mirror_stderr, alm_stderr,
                "{name}: front diagnostics diverged from mirror"
            );
        } else {
            // A later-tier negative case: the front end must accept it
            // (alm silent, exit 0), and mirror's own stderr carries no
            // Syntax-tier line — the refusal belongs to a stage alm has
            // not ported (Modules/Ffi/Analyze/Lower).
            let mut alm_args = case.surface_flags();
            alm_args.push(case.path.display().to_string());
            let alm = run(&mine, &alm_args);
            assert!(
                alm.status.success() && alm.stdout.is_empty() && alm.stderr.is_empty(),
                "{name}: not a front refusal, but alm's front end spoke:\n{}",
                String::from_utf8_lossy(&alm.stderr)
            );
            let mirror_stderr = without_trace_pokes(&mirror.stderr);
            assert!(
                !mirror_stderr
                    .lines()
                    .any(|l| l.contains(": Syntax Error: ")),
                "{name}: mirror refuses at the syntax tier but the catalog \
                 missed it — FRONT_REFUSALS is stale"
            );
        }
    }
    assert_eq!(
        checked,
        common::FRONT_REFUSALS.len(),
        "not every catalogued front refusal ran"
    );
}

#[test]
fn corpus_front_sweep_parses_clean_where_mirror_accepts() {
    let root = cases_dir();
    let mut files = Vec::new();
    collect_lua_files(&root, &mut files);
    files.sort();
    assert!(
        files.len() >= 440,
        "corpus shrank to {} files — the frozen corpus of record is 449",
        files.len(),
    );

    let mut refused: Vec<String> = Vec::new();
    for path in &files {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(path).unwrap();
        let first = parse_on_big_stack(path.clone(), text.clone());
        if !first.diagnostics.is_empty() {
            if !is_front_refusal(&name) {
                refused.push(format!("{name}: {}", first.diagnostics[0].render()));
            }
            continue;
        }
        // Determinism: an identical re-parse dumps byte-identically.
        let again = parse_on_big_stack(path.clone(), text);
        assert_eq!(
            render_ast(&first.ast),
            render_ast(&again.ast),
            "{name}: re-parse diverged"
        );
    }

    assert!(
        refused.is_empty(),
        "{} corpus files refused at the front outside the frozen catalog: {}",
        refused.len(),
        refused.join(" | "),
    );
}
