//! L6b's leg (`L6_BRIEF_6.4.md` §2): the omni watcher's observer law
//! (`L6_DESIGN.md` law 7), subprocess against subprocess over the
//! 449-file corpus.
//!
//! In-process legs cannot test the watcher: `enabled()` is a
//! process-wide `OnceLock`, read once. So every run here is a child
//! process — alm's **release** binary (`ALM_BIN`, else
//! `target/release/alm`; `cargo test` does not rebuild it) and the
//! frozen oracle — each from its own scratch cwd.
//!
//! Four runs per file, each with the case's FLAGS and
//! `--module-root=<cases>/modules`; alm's take `--dump-shape` (the
//! oracle has no dump — it compiles, links and runs its artifact):
//!
//! | run | binary | environment |
//! |---|---|---|
//! | a | alm | watcher variables removed |
//! | b | alm | `ALM_OMNI=1` |
//! | c | alm | `ALM_OMNI=1`, `ALM_OMNI_STRICT=1` |
//! | o | oracle | `ALM_OMNI=1` |
//!
//! The report line (`omni.rs`, `finish`) is
//! `[omni] events: N · trips: orphan-burial A (hard) · root-drag B
//! (soft) · chain-freeze C (hard)`. The assertions, in order:
//!
//! 1. **Liveness, once** — the canary's b-run carries the report
//!    header and a report line. A release binary without the watcher
//!    fails here by name instead of passing vacuously.
//! 2. **The observer law, per file** — exit status, stdout and stderr
//!    (every `[omni]` line removed) identical across a / b / c; c
//!    never exits 101 (a hard trip's panic under STRICT) or on a
//!    signal.
//! 3. **No hard trip, per file** — orphan-burial 0, chain-freeze 0.
//! 4. **Against the oracle, per file** — the same (orphan, drag,
//!    chain) on every file, and the census the brief pre-registered:
//!    0 / 3 / 0 over the corpus, the three drags all in the canary.
//!    ROOT-DRAG is soft and chartered: it is asserted equal to the
//!    oracle's, never zero.
//! 5. **Events, per file** — the same `N` on every file, and the
//!    corpus total the oracle's (12,207).
//!
//! `--dump-shape` exits 1 on a refusal by design — 124 corpus files —
//! so the law asserts "status unchanged across configurations", never
//! "exit 0". A file the front end or the require splice refuses never
//! reaches the analysis and prints no report in either binary (27 of
//! them); a missing report reads as zeros, and assertions 4 and 5
//! compare the report's presence as well, so one side missing it
//! cannot pass as agreement.
//!
//! Printed and not asserted: whether the `[omni]` lines themselves are
//! byte-identical between b and o. Measured at 6.4: identical on every
//! file. The leg freezes what the brief names — the count — because an
//! event line carries `fn#NodeId` tokens, which are the front end's,
//! not the watcher's.

mod common;

use common::{cases_dir, collect_lua_files, module_root};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output};
use std::sync::atomic::{AtomicU64, Ordering};

/// The one corpus file the watcher trips on (three root-drags), and
/// the file the liveness assertion reads.
const CANARY: &str = "fn_defcollection_order.lua";

/// The oracle's census over the corpus of record (`L6_BRIEF_6.4.md`
/// §2), measured against the oracle before the port.
const ORACLE_EVENTS: u64 = 12_207;
const ORACLE_DRAGS: u64 = 3;

const HEADER: &str = "[omni] ══ omni report ══";

fn alm_bin() -> PathBuf {
    if let Ok(custom) = std::env::var("ALM_BIN") {
        return PathBuf::from(custom);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/release/alm")
}

fn oracle_bin() -> PathBuf {
    let p = cases_dir()
        .parent()
        .expect("corpus root has a parent")
        .join("target/release/alm");
    assert!(
        p.is_file(),
        "the frozen oracle is missing — rebuild it: \
         (cd ../mirror_experimental && cargo build --release)"
    );
    p
}

/// One report line's four numbers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Report {
    events: u64,
    orphan: u64,
    drag: u64,
    chain: u64,
}

impl Report {
    const ZERO: Report = Report {
        events: 0,
        orphan: 0,
        drag: 0,
        chain: 0,
    };

    fn trips(self) -> (u64, u64, u64) {
        (self.orphan, self.drag, self.chain)
    }

    fn add(self, other: Report) -> Report {
        Report {
            events: self.events + other.events,
            orphan: self.orphan + other.orphan,
            drag: self.drag + other.drag,
            chain: self.chain + other.chain,
        }
    }
}

/// `[omni] events: N · trips: orphan-burial A (hard) · root-drag B
/// (soft) · chain-freeze C (hard)` — the watcher's own wording.
fn parse_report(line: &str) -> Option<Report> {
    let rest = line.strip_prefix("[omni] events: ")?;
    let (events, rest) = rest.split_once(" · trips: orphan-burial ")?;
    let (orphan, rest) = rest.split_once(" (hard) · root-drag ")?;
    let (drag, rest) = rest.split_once(" (soft) · chain-freeze ")?;
    let (chain, tail) = rest.split_once(" (hard)")?;
    if !tail.is_empty() {
        return None;
    }
    Some(Report {
        events: events.parse().ok()?,
        orphan: orphan.parse().ok()?,
        drag: drag.parse().ok()?,
        chain: chain.parse().ok()?,
    })
}

/// One child process's output, read for the law.
struct Run {
    status: ExitStatus,
    stdout: Vec<u8>,
    /// stderr verbatim.
    raw: String,
    /// stderr without its `[omni]` lines — what the observer law
    /// compares.
    stderr: String,
    /// One entry per report line; `None` for one that did not parse.
    reports: Vec<Option<Report>>,
}

impl Run {
    fn new(
        Output {
            status,
            stdout,
            stderr,
        }: Output,
    ) -> Self {
        let raw = String::from_utf8_lossy(&stderr).into_owned();
        let mut kept = String::with_capacity(raw.len());
        let mut reports = Vec::new();
        for line in raw.lines() {
            match line.strip_prefix("[omni]") {
                Some(rest) if rest.starts_with(" events: ") => {
                    reports.push(parse_report(line));
                }
                Some(_) => {}
                None => {
                    kept.push_str(line);
                    kept.push('\n');
                }
            }
        }
        Run {
            status,
            stdout,
            raw,
            stderr: kept,
            reports,
        }
    }

    /// The run's report: `Ok(None)` when it printed none — a file the
    /// front end or the splice refuses never reaches the analysis.
    fn report(&self) -> Result<Option<Report>, String> {
        match self.reports.as_slice() {
            [] => Ok(None),
            [Some(report)] => Ok(Some(*report)),
            _ => Err(format!(
                "{} report line(s), a malformed one among them",
                self.reports.len()
            )),
        }
    }

    /// The watcher's own lines of stderr, in order.
    fn omni_lines(&self) -> Vec<&str> {
        self.raw
            .lines()
            .filter(|line| line.starts_with("[omni]"))
            .collect()
    }
}

static RUNS: AtomicU64 = AtomicU64::new(0);

/// The child's environment carries exactly the watcher variables asked
/// for, and no others.
fn watcher_env(mut cmd: Command, omni: Option<&str>, strict: bool) -> Command {
    cmd.env_remove("ALM_OMNI").env_remove("ALM_OMNI_STRICT");
    if let Some(value) = omni {
        cmd.env("ALM_OMNI", value);
    }
    if strict {
        cmd.env("ALM_OMNI_STRICT", "1");
    }
    cmd
}

/// One child process from its own scratch directory (`L6_HARNESS.md`
/// §2 — the oracle writes its plate and its artifact there), removed
/// once it has been read. The oracle runs under core limit 0: it
/// aborts by design on 17 corpus cases.
fn spawn(bin: &Path, args: &[String], omni: Option<&str>, strict: bool, core_limit: bool) -> Run {
    let scratch = std::env::temp_dir().join(format!(
        "alm_l6_omni_scratch_{}_{}",
        std::process::id(),
        RUNS.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&scratch).expect("omni scratch dir");
    let cmd = if core_limit {
        let mut sh = Command::new("sh");
        sh.args(["-c", "ulimit -c 0 && exec \"$@\"", "sh"])
            .arg(bin)
            .args(args)
            .current_dir(&scratch);
        sh
    } else {
        let mut direct = Command::new(bin);
        direct.args(args).current_dir(&scratch);
        direct
    };
    let output = watcher_env(cmd, omni, strict).output();
    let _ = std::fs::remove_dir_all(&scratch);
    Run::new(output.unwrap_or_else(|e| panic!("running {} failed: {e}", bin.display())))
}

/// One corpus case: its path and the FLAGS words of its `--` header.
struct Case {
    path: PathBuf,
    flags: Vec<String>,
}

impl Case {
    /// Header scanning in Rust, binary-safe: one corpus case carries a
    /// raw NUL, which `grep -l` drops silently.
    fn read(path: &Path) -> Self {
        let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
        let flags = bytes
            .split(|b| *b == b'\n')
            .find_map(|line| line.strip_prefix(b"-- FLAGS:"))
            .map(|rest| {
                String::from_utf8_lossy(rest)
                    .split_whitespace()
                    .map(str::to_string)
                    .collect()
            })
            .unwrap_or_default();
        Case {
            path: path.to_path_buf(),
            flags,
        }
    }

    /// alm's words: the surface flags and the link mode (the ffi gate
    /// reads `--exe` / `--lib`). A header's `--module-root=` is
    /// relative to the corpus's own tree, so it is skipped for alm and
    /// the leg passes the absolute root.
    fn alm_args(&self) -> Vec<String> {
        let mut args: Vec<String> = self
            .flags
            .iter()
            .filter(|flag| {
                flag.starts_with("--index-base=")
                    || flag.starts_with("--for-limit=")
                    || matches!(flag.as_str(), "--exe" | "--lib")
            })
            .cloned()
            .collect();
        args.push("--dump-shape".to_string());
        args.push(format!("--module-root={}", module_root().display()));
        args.push(self.path.display().to_string());
        args
    }

    /// The oracle's words: every FLAGS word, then the module root —
    /// mirror's last-flag-wins law replaces a header's relative one.
    fn oracle_args(&self) -> Vec<String> {
        let mut args = self.flags.clone();
        args.push(format!("--module-root={}", module_root().display()));
        args.push(self.path.display().to_string());
        args
    }
}

/// The first line two texts disagree on, for a failure message.
fn first_diff(left: &str, right: &str) -> String {
    let (left, right) = (
        left.lines().collect::<Vec<_>>(),
        right.lines().collect::<Vec<_>>(),
    );
    (0..left.len().max(right.len()))
        .map(|i| (left.get(i).copied(), right.get(i).copied()))
        .find(|(l, r)| l != r)
        .map(|(l, r)| {
            format!(
                "\n    a:   {}\n    b/c: {}",
                l.unwrap_or("<end of stderr>"),
                r.unwrap_or("<end of stderr>")
            )
        })
        .unwrap_or_default()
}

/// A failure list for a message: its first rows, then how many more.
fn listed(failures: &[String]) -> String {
    const SHOWN: usize = 25;
    let mut text = failures
        .iter()
        .take(SHOWN)
        .cloned()
        .collect::<Vec<_>>()
        .join("\n  ");
    if failures.len() > SHOWN {
        text.push_str(&format!("\n  … and {} more", failures.len() - SHOWN));
    }
    text
}

/// A run's report for the census: the report (zeros when none), and
/// whether one was printed. None printed is legal — a file the front
/// end or the splice refuses never reaches the analysis; a malformed
/// or doubled report line is a failure, recorded under `failures`.
fn census_report(run: &Run, failures: &mut Vec<String>, name: &str, whose: &str) -> (Report, bool) {
    match run.report() {
        Ok(Some(report)) => (report, true),
        Ok(None) => (Report::ZERO, false),
        Err(why) => {
            failures.push(format!("{name}: {whose} {why}"));
            (Report::ZERO, false)
        }
    }
}

#[test]
fn omni_watcher_observes_without_touching() {
    let mine = alm_bin();
    assert!(
        mine.is_file(),
        "alm release binary {} missing — build it first: cargo build --release",
        mine.display()
    );
    let oracle = oracle_bin();

    let root = cases_dir();
    let mut files = Vec::new();
    collect_lua_files(&root, &mut files);
    files.sort();
    assert!(
        files.len() >= 449,
        "corpus pool shrank: {} — the corpus of record is 449",
        files.len()
    );
    let canary_path = root.join(CANARY);
    assert!(
        canary_path.is_file(),
        "the canary {CANARY} is not in the corpus"
    );

    // 1. Liveness, once: the canary's b-run must carry the report.
    let canary = Case::read(&canary_path);
    let live = spawn(&mine, &canary.alm_args(), Some("1"), false, false);
    let alive = live.raw.lines().any(|line| line == HEADER) && matches!(live.report(), Ok(Some(_)));
    assert!(
        alive,
        "the release binary predates the watcher — run `cargo build --release` \
         ({}: no `[omni]` report under ALM_OMNI=1; exit {:?})",
        mine.display(),
        live.status
    );

    // 2–5, per file. Each assertion keeps its own list, and the lists
    // are checked in the brief's order.
    let mut law_broke = Vec::new();
    let mut hard_trips = Vec::new();
    let mut oracle_differs = Vec::new();
    let mut events_differ = Vec::new();
    let mut alm_trips = Report::ZERO;
    let mut oracle_trips = Report::ZERO;
    let mut alm_events = 0u64;
    let mut oracle_events = 0u64;
    let mut drag_files = Vec::new();
    let mut reports = 0usize;
    let mut statuses = std::collections::BTreeMap::new();
    let mut line_diffs = 0usize;
    let mut at_cap = 0usize;

    for path in &files {
        let name = path
            .strip_prefix(&root)
            .ok()
            .and_then(|r| r.to_str())
            .map(|r| r.replace('\\', "/"))
            .unwrap_or_default();
        let case = Case::read(path);
        let alm_args = case.alm_args();
        let a = spawn(&mine, &alm_args, None, false, false);
        let b = spawn(&mine, &alm_args, Some("1"), false, false);
        let c = spawn(&mine, &alm_args, Some("1"), true, false);
        let o = spawn(&oracle, &case.oracle_args(), Some("1"), false, true);

        // 2. the observer law
        if a.status != b.status || a.status != c.status {
            law_broke.push(format!(
                "{name}: status a={:?} b={:?} c={:?}",
                a.status, b.status, c.status
            ));
        }
        if a.stdout != b.stdout || a.stdout != c.stdout {
            law_broke.push(format!(
                "{name}: stdout moved with the watcher on ({} / {} / {} bytes)",
                a.stdout.len(),
                b.stdout.len(),
                c.stdout.len()
            ));
        }
        if a.stderr != b.stderr {
            law_broke.push(format!(
                "{name}: stderr moved with the watcher on, [omni] lines removed:{}",
                first_diff(&a.stderr, &b.stderr)
            ));
        }
        if a.stderr != c.stderr {
            law_broke.push(format!(
                "{name}: stderr moved under STRICT, [omni] lines removed:{}",
                first_diff(&a.stderr, &c.stderr)
            ));
        }
        if c.status.code() == Some(101) || c.status.signal().is_some() {
            law_broke.push(format!(
                "{name}: STRICT exited {:?} — a hard trip panicked, or a signal",
                c.status
            ));
        }
        *statuses.entry(a.status.code()).or_insert(0usize) += 1;

        // 3. no hard trip, from b's report line
        let (rb, printed_b) = census_report(&b, &mut hard_trips, &name, "alm's");
        if rb.orphan != 0 || rb.chain != 0 {
            hard_trips.push(format!(
                "{name}: orphan-burial {} · chain-freeze {} (hard)",
                rb.orphan, rb.chain
            ));
        }

        // 4. against the oracle
        let (ro, printed_o) = census_report(&o, &mut oracle_differs, &name, "the oracle's");
        if rb.trips() != ro.trips() || printed_b != printed_o {
            oracle_differs.push(format!(
                "{name}: trips orphan/drag/chain alm {:?} ({}) / oracle {:?} ({})",
                rb.trips(),
                printed_b,
                ro.trips(),
                printed_o
            ));
        }

        // 5. events
        if rb.events != ro.events || printed_b != printed_o {
            events_differ.push(format!(
                "{name}: events alm {} / oracle {}",
                rb.events, ro.events
            ));
        }

        // the census
        alm_trips = alm_trips.add(rb);
        oracle_trips = oracle_trips.add(ro);
        alm_events += rb.events;
        oracle_events += ro.events;
        if rb.drag != 0 {
            drag_files.push(name.clone());
        }
        if printed_b {
            reports += 1;
        }
        if rb.events >= 4096 {
            at_cap += 1;
        }
        if b.omni_lines() != o.omni_lines() {
            line_diffs += 1;
        }
    }

    assert!(
        law_broke.is_empty(),
        "the observer law broke on {} file(s) — a hook changed behaviour; \
         find it before anything else:\n  {}",
        law_broke.len(),
        listed(&law_broke)
    );
    assert!(
        hard_trips.is_empty(),
        "{} file(s) under a hard trip (or with no readable report):\n  {}",
        hard_trips.len(),
        listed(&hard_trips)
    );
    assert!(
        oracle_differs.is_empty(),
        "{} file(s) trip differently from the oracle:\n  {}",
        oracle_differs.len(),
        listed(&oracle_differs)
    );
    assert_eq!(
        oracle_trips.trips(),
        (0, ORACLE_DRAGS, 0),
        "the oracle's census moved off the pre-registered 0 / 3 / 0"
    );
    assert_eq!(
        alm_trips.trips(),
        oracle_trips.trips(),
        "alm's census is not the oracle's"
    );
    assert_eq!(
        drag_files,
        [CANARY.to_string()],
        "the root-drags are not all the canary's"
    );
    assert!(
        events_differ.is_empty(),
        "{} file(s) whose event count differs from the oracle's — a hook at \
         the wrong point:\n  {}",
        events_differ.len(),
        listed(&events_differ)
    );
    assert_eq!(
        oracle_events, ORACLE_EVENTS,
        "the oracle's events total moved"
    );
    assert_eq!(
        alm_events, oracle_events,
        "alm's events total is not the oracle's"
    );

    eprintln!(
        "omni: {} files · 4 runs each · events {} / {} (oracle) · orphan-burial {} \
         · root-drag {} ({}) · chain-freeze {} · reports {} · at the 4096 cap {} \
         · [omni] lines byte-identical {} / {} · alm exit statuses {:?}",
        files.len(),
        alm_events,
        oracle_events,
        alm_trips.orphan,
        alm_trips.drag,
        alm_trips.drag == oracle_trips.drag && drag_files == [CANARY.to_string()],
        alm_trips.chain,
        reports,
        at_cap,
        reports - line_diffs,
        reports,
        statuses
    );
}
