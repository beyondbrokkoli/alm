//! Shared corpus idioms for the L2+ harness legs (integration tests
//! include this via `mod common;`). Each test crate compiles its own
//! copy, so a leg that needs half the helpers would dead-code the rest
//! — the allowance below is the module's, not any layer's.
#![allow(dead_code)]

use alm::analysis::build_context;
use alm::ast::{NodeId, Stmt};
use alm::pipeline::front;
use alm::shape::ShapeFacts;
use alm::source::SourceFile;
use alm::surface::{Flag, Surface};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

pub fn cases_dir() -> PathBuf {
    if let Ok(custom) = std::env::var("ALM_MIRROR_CASES") {
        return PathBuf::from(custom);
    }
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../mirror_experimental/cases")
}

/// The module tree the corpus's require cases anchor against (the
/// plan's 8 module fixtures live under `cases/modules/`).
pub fn module_root() -> PathBuf {
    cases_dir().join("modules")
}

pub fn collect_lua_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("corpus dir {} unreadable: {e}", dir.display()));
    for entry in entries {
        let path = entry.expect("corpus entry").path();
        if path.is_dir() {
            collect_lua_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "lua") {
            out.push(path);
        }
    }
}

/// The deterministic xorshift64* generator (mirror's property harness,
/// verbatim) — the mutation and purity legs' base pool.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self(seed | 1)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub fn below(&mut self, n: usize) -> usize {
        debug_assert!(n > 0, "Rng::below called with n == 0");
        ((u128::from(self.next()) * u128::from(n as u64)) >> 64) as usize
    }
}

pub fn fnv1a(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in bytes {
        h ^= u64::from(*b);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// The witness kinds mirror's `gen_program` draws from (the Elem
/// machinery's `.ll`-facing projections — esize/kind flags, the
/// assert_elem_congruence oracle — are L7+ and never port here).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Elem {
    Int,
    Flt,
    Bool,
    Str,
    Any,
}

impl Elem {
    fn join(self, other: Elem) -> Elem {
        if self == other { self } else { Elem::Any }
    }

    fn lit(self, rng: &mut Rng) -> &'static str {
        match self {
            Elem::Int => ["3", "7"][rng.below(2)],
            Elem::Flt => ["2.5", "0.5"][rng.below(2)],
            Elem::Bool => ["true", "false"][rng.below(2)],
            Elem::Str => ["\"s\"", "\"w\""][rng.below(2)],
            Elem::Any => unreachable!("literals are per-kind, Any only arises by joining"),
        }
    }
}

fn witness_kind(rng: &mut Rng) -> Elem {
    [Elem::Int, Elem::Flt, Elem::Bool, Elem::Str][rng.below(4)]
}

fn pick_witness_kind(rng: &mut Rng, locked: Option<Elem>) -> Elem {
    locked.unwrap_or_else(|| witness_kind(rng))
}

fn record_witness(kind: Elem, elem: &mut Option<Elem>) {
    *elem = Some(match *elem {
        Some(e) => e.join(kind),
        None => kind,
    });
}

/// The table-program generator (mirror's `gen_program`, verbatim — the
/// purity leg's generated bases).
pub fn gen_program(rng: &mut Rng) -> String {
    let mut elem: Option<Elem> = None;
    let mut lines: Vec<String> = Vec::new();

    let locked: Option<Elem> = if rng.below(20) < 9 {
        Some(witness_kind(rng))
    } else {
        None
    };

    if rng.below(5) == 0 {
        lines.push("local t = {}".to_string());
        let k0 = pick_witness_kind(rng, locked);
        record_witness(k0, &mut elem);
        lines.push(format!("t[{}] = {}", rng.below(8), k0.lit(rng)));
    } else {
        let mixed = locked.is_none() && rng.below(4) == 0;
        let n = 1 + rng.below(2);
        let k0 = pick_witness_kind(rng, locked);
        let entries: Vec<String> = (0..n)
            .map(|i| {
                let k = if mixed && i == 1 {
                    pick_witness_kind(rng, locked)
                } else {
                    k0
                };
                record_witness(k, &mut elem);
                k.lit(rng).to_string()
            })
            .collect();
        lines.push(format!("local t = {{{}}}", entries.join(", ")));
    }

    let stmts = 2 + rng.below(6);
    for _ in 0..stmts {
        match rng.below(11) {
            0 => {
                let k = pick_witness_kind(rng, locked);
                record_witness(k, &mut elem);
                lines.push(format!("t[{}] = {}", rng.below(8), k.lit(rng)));
            }
            1 | 2 => lines.push(format!("print(t[{}])", rng.below(8))),
            3 => lines.push("print(#t)".to_string()),
            4 | 5 => {
                lines.push(ctor_line(rng, locked, &mut elem));
            }
            6 => {
                lines.push("t = nil".to_string());
                lines.push(ctor_line(rng, locked, &mut elem));
            }
            7 => {
                let body = branch_body(rng, locked, &mut elem);
                if rng.below(2) == 0 {
                    let cond = ["true", "false"][rng.below(2)];
                    lines.push(format!("if {cond} then\n{body}\nend"));
                } else {
                    lines.push(format!("do\n{body}\nend"));
                }
            }
            8 | 9 => {
                let cond = ["true", "false"][rng.below(2)];
                let then_body = branch_body(rng, locked, &mut elem);
                let else_body = branch_body(rng, locked, &mut elem);
                lines.push(format!(
                    "if {cond} then\n{then_body}\nelse\n{else_body}\nend"
                ));
            }
            _ => {
                let bound = 2 + rng.below(4);
                match rng.below(3) {
                    0 => {
                        let k = pick_witness_kind(rng, locked);
                        record_witness(k, &mut elem);
                        lines.push(format!(
                            "for i = 0, {bound} do\n  t[i] = {}\nend",
                            k.lit(rng)
                        ));
                    }
                    1 => lines.push(format!("for i = 0, {bound} do\n  print(t[i])\nend")),
                    _ => {
                        let k = pick_witness_kind(rng, locked);
                        record_witness(k, &mut elem);
                        let cond = ["true", "false"][rng.below(2)];
                        lines.push(format!(
                            "while {cond} do\n  t[{}] = {}\n  break\nend",
                            rng.below(8),
                            k.lit(rng)
                        ));
                    }
                }
            }
        }
    }

    lines.push(format!("print(t[{}])", rng.below(8)));

    let _ = elem.expect("the opening sequence always witnesses at least one kind");
    lines.join("\n") + "\n"
}

fn branch_body(rng: &mut Rng, locked: Option<Elem>, elem: &mut Option<Elem>) -> String {
    match rng.below(4) {
        0 => {
            let k = pick_witness_kind(rng, locked);
            record_witness(k, elem);
            format!("t[{}] = {}", rng.below(8), k.lit(rng))
        }
        1 => format!("print(t[{}])", rng.below(8)),
        2 => ctor_line(rng, locked, elem),
        _ => {
            let rebind = ctor_line(rng, locked, elem);
            format!("t = nil\n{rebind}")
        }
    }
}

fn ctor_line(rng: &mut Rng, locked: Option<Elem>, elem: &mut Option<Elem>) -> String {
    let n = rng.below(3);
    if n == 0 {
        return "t = {}".to_string();
    }
    let k0 = pick_witness_kind(rng, locked);
    let entries: Vec<String> = (0..n)
        .map(|i| {
            let k = if i == 1 && locked.is_none() && rng.below(2) == 0 {
                pick_witness_kind(rng, locked)
            } else {
                k0
            };
            record_witness(k, elem);
            k.lit(rng).to_string()
        })
        .collect();
    format!("t = {{{}}}", entries.join(", "))
}

/// Parse helper for the in-process pins (mirror's `parse_parts`,
/// adapted): a diagnostic-free parse or the test dies.
pub fn parse_parts(source: &str) -> Vec<alm::ast::Stmt> {
    let src = SourceFile::new("pin.lua", source);
    let out = front(&src, &Surface::default());
    assert!(
        out.diagnostics.is_empty(),
        "pin source must parse clean: {:?}",
        out.diagnostics
    );
    out.ast
}

/// The L3+ analyze leg's driver: front + splice + walk + checker with
/// the `walk_pins` lever, on a thread with the sweep's stack headroom.
/// A panic maps to `Stage::Panicked` exactly as mirror's catch_unwind
/// harness does. The case's `--exe`/`--lib` FLAGS ride along (the ffi
/// gate's law).
pub fn analyze_with_lever(
    path: String,
    text: String,
    walk_pins: bool,
) -> Result<String, (alm::pipeline::Stage, String)> {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let surface = surface_flags_of(&text);
            let standalone = standalone_of(&text);
            let src = SourceFile::new(path, text);
            let root = module_root();
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                alm::pipeline::analyze_stage(&src, &surface, Some(&root), walk_pins, standalone)
            })) {
                Ok(Ok(out)) => Ok(alm::dump::render_shape(&out.facts, &out.ast)),
                Ok(Err((stage, diags))) => {
                    let text = diags
                        .iter()
                        .map(|d| d.render())
                        .collect::<Vec<_>>()
                        .join("\n");
                    Err((stage, text))
                }
                Err(_) => Err((alm::pipeline::Stage::Panicked, String::new())),
            }
        })
        .expect("spawn sweep thread")
        .join()
        .unwrap_or_else(|_| Err((alm::pipeline::Stage::Panicked, "thread panicked".into())))
}

/// The case's link mode from its `-- FLAGS:` header — `--exe` arms
/// standalone (exempting the ffi gate), `--lib` or nothing is the
/// default shared-library mode. Last flag wins, mirror's law.
pub fn standalone_of(text: &str) -> bool {
    let mut standalone = false;
    for word in text
        .lines()
        .find_map(|l| l.strip_prefix("-- FLAGS:"))
        .into_iter()
        .flat_map(str::split_whitespace)
    {
        match word {
            "--exe" => standalone = true,
            "--lib" => standalone = false,
            _ => {}
        }
    }
    standalone
}

/// The frozen front-refusal catalog: corpus files the front end (lex +
/// parse + desugar) rejects — verified against mirror's compiled
/// binary, stderr byte-exact. Classification is front-truth, not a
/// stderr prefix: the checker also mints `Table Bounds Error`
/// (`exprkey_const_bounds`, `shape_errors`, `ffi_static_key_over_capacity`
/// refuse there — mirror's Stage::Front stops first), so prefix
/// matching over-approximates. 19 files.
pub const FRONT_REFUSALS: &[&str] = &[
    "assign_target_rejected.lua",
    "continue_rejected.lua",
    "ctor_dup_index_rejected.lua",
    "ctor_dup_key_spellings_rejected.lua",
    "desugar_hygiene_dollar_rejected.lua",
    "fn_sugar_colon_rejected.lua",
    "fn_varargs_rejected.lua",
    "for_float_bound_rejected.lua",
    "for_step_rejected.lua",
    "for_var_nested_while_rejected.lua",
    "index_base1_ctor_dup_rejected.lua",
    "index_base1_ctor_dup_zero_key_rejected.lua",
    "local_arity_mismatch_rejected.lua",
    "nul_string.lua",
    "parser_depth_ctor_rejected.lua",
    "parser_depth_rejected.lua",
    "parser_syntax_bail.lua",
    "tuple_count_mismatch_rejected.lua",
    "tuple_name_for_var_rejected.lua",
];

pub fn is_front_refusal(name: &str) -> bool {
    FRONT_REFUSALS.contains(&name)
}

/// The L2 surface flags carried in a case's `-- FLAGS:` header; later
/// layers' flags are not the front end's to read. Unknown-to-L2 words
/// are skipped, not refused — the corpus pins them for their owners.
pub fn surface_flags_of(text: &str) -> Surface {
    let mut surface = Surface::default();
    for word in text
        .lines()
        .find_map(|l| l.strip_prefix("-- FLAGS:"))
        .into_iter()
        .flat_map(str::split_whitespace)
    {
        if let Ok(flag) = Flag::parse(word) {
            flag.apply(&mut surface);
        }
    }
    surface
}

/// Front-parses `text` on a thread with explicit stack headroom: the
/// depth-guard cases recurse ~10 frames per nesting level to the
/// MAX_EXPR_DEPTH limit (1024) — comfortable on release frames or an
/// 8 MiB main thread, but not on a libtest worker's debug frames. The
/// guard is the dialect's, not the harness's; this changes no parser
/// behavior.
pub fn parse_on_big_stack(path: PathBuf, text: String) -> alm::pipeline::FrontOutput {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let src = SourceFile::new(path.display().to_string(), text);
            front(&src, &surface_flags_of(src.text()))
        })
        .expect("spawn sweep thread")
        .join()
        .expect("sweep thread panicked")
}

// — the L6 harness (L6_HARNESS.md §3–§5): the oracle plate, the pins'
// driver and the lease helper.

/// The oracle's exit-family pokes for one program, a count per family
/// — what its trace plate says it minted (L6_HARNESS.md §3). The
/// fields follow the registry's slot order; `count_exit_families` is
/// alm's side of the same table.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ExitCounts {
    pub do_exit: u32,
    pub stmt_temp: u32,
    pub root_exit: u32,
    pub ret_path: u32,
    pub cond_temp: u32,
    pub arm_temp: u32,
    pub ret_keep: u32,
    pub arm_split: u32,
    /// No fact records a scalar skip — the oracle's number rides for
    /// the census alone.
    pub scalar_skip: u32,
}

impl ExitCounts {
    /// Two programs' counts summed — the corpus totals.
    pub fn add(self, other: ExitCounts) -> ExitCounts {
        ExitCounts {
            do_exit: self.do_exit + other.do_exit,
            stmt_temp: self.stmt_temp + other.stmt_temp,
            root_exit: self.root_exit + other.root_exit,
            ret_path: self.ret_path + other.ret_path,
            cond_temp: self.cond_temp + other.cond_temp,
            arm_temp: self.arm_temp + other.arm_temp,
            ret_keep: self.ret_keep + other.ret_keep,
            arm_split: self.arm_split + other.arm_split,
            scalar_skip: self.scalar_skip + other.scalar_skip,
        }
    }
}

/// The trace registry's slot ids by signal name: `<slot> <NAME> <tier>
/// <text>` rows, comments and blanks ignored. Slots are looked up by
/// name, never hard-coded.
fn trace_slots(registry: &str) -> BTreeMap<&str, u8> {
    registry
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .filter_map(|l| {
            let mut fields = l.split_whitespace();
            let slot = fields.next()?.parse().ok()?;
            Some((fields.next()?, slot))
        })
        .collect()
}

/// Decodes the compiler trace plate: `fired` and `capacity` (u32,
/// little-endian), then the ring — one slot id per poke. A ring that
/// wrapped is rotated, so it fails loudly instead of counting a
/// truncated chronology (no corpus case wraps; the busiest records
/// 3,555 of 8,192).
fn plate_pokes(plate: &[u8]) -> BTreeMap<u8, u32> {
    let word =
        |at: usize| u32::from_le_bytes(plate[at..at + 4].try_into().expect("a plate header word"));
    assert!(
        plate.len() >= 8,
        "the trace plate is {} bytes — truncated",
        plate.len()
    );
    let (fired, capacity) = (word(0), word(4));
    assert!(
        fired <= capacity,
        "the oracle's trace plate wrapped: {fired} pokes in a ring of {capacity}"
    );
    assert_eq!(
        plate.len(),
        8 + capacity as usize,
        "the trace plate is {} bytes, not 8 + {capacity}",
        plate.len()
    );
    let mut pokes: BTreeMap<u8, u32> = BTreeMap::new();
    for &slot in &plate[8..8 + fired as usize] {
        *pokes.entry(slot).or_insert(0) += 1;
    }
    pokes
}

/// One oracle run: the process's output and the scratch directory it
/// ran in — the plate lands there, and the caller removes it once the
/// run is read.
struct OracleRun {
    out: std::process::Output,
    scratch: PathBuf,
}

/// Spawns the oracle on one program (L6_HARNESS.md §2): a corpus file
/// compiles from its own path; anything else is `name` written into a
/// scratch directory, so a pin can pass its source. One directory per
/// run — the plate lands in the oracle's working directory, so two
/// runs sharing one would read each other's plate (the pins call this
/// in parallel). The run takes the case's FLAGS, the module root, core
/// limit 0 (the oracle aborts by design on 17 cases) and no watcher
/// variables.
fn run_oracle(name: &str, text: &str) -> OracleRun {
    let cases = cases_dir();
    let binary = cases
        .parent()
        .expect("corpus root has a parent")
        .join("target/release/alm");
    assert!(
        binary.is_file(),
        "the frozen oracle is missing — rebuild it: \
         (cd ../mirror_experimental && cargo build --release)"
    );

    static RUNS: AtomicU64 = AtomicU64::new(0);
    let scratch = std::env::temp_dir().join(format!(
        "alm_l6_oracle_scratch_{}_{}",
        std::process::id(),
        RUNS.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&scratch).expect("oracle scratch dir");

    let own_path = cases.join(name);
    let file = if own_path.is_file() {
        own_path
    } else {
        let written = scratch.join(name);
        if let Some(parent) = written.parent() {
            std::fs::create_dir_all(parent).expect("oracle input dir");
        }
        std::fs::write(&written, text).expect("write the oracle's input");
        written
    };

    let flags: Vec<String> = text
        .lines()
        .find_map(|l| l.strip_prefix("-- FLAGS:"))
        .into_iter()
        .flat_map(str::split_whitespace)
        .map(str::to_string)
        .collect();
    let out = std::process::Command::new("sh")
        .args(["-c", "ulimit -c 0 && exec \"$@\"", "sh"])
        .arg(&binary)
        .args(&flags)
        .arg(format!("--module-root={}", module_root().display()))
        .arg(&file)
        .current_dir(&scratch)
        .env_remove("ALM_OMNI")
        .env_remove("ALM_OMNI_STRICT")
        .output()
        .unwrap_or_else(|e| panic!("running the oracle {} failed: {e}", binary.display()));
    OracleRun { out, scratch }
}

/// The oracle's own count of the exit facts it minted for one program
/// (L6_HARNESS.md §3). mirror has no facts dump, but it writes a
/// trace plate unconditionally and the exit-family slots are poked
/// only from `exits.rs`.
pub fn oracle_exit_counts(name: &str, text: &str) -> ExitCounts {
    let OracleRun { out, scratch } = run_oracle(name, text);
    let plate = std::fs::read(scratch.join(".alm_trace.bin")).unwrap_or_else(|e| {
        panic!(
            "the oracle left no trace plate ({}): {e} — exit {out:?}",
            scratch.display()
        )
    });
    let _ = std::fs::remove_dir_all(&scratch);

    let registry_path = cases_dir()
        .parent()
        .expect("corpus root has a parent")
        .join("trace_signals.txt");
    let registry = std::fs::read_to_string(&registry_path)
        .unwrap_or_else(|e| panic!("{} unreadable: {e}", registry_path.display()));
    let slots = trace_slots(&registry);
    let pokes = plate_pokes(&plate);
    let count = |signal: &str| {
        let slot = slots
            .get(signal)
            .unwrap_or_else(|| panic!("the trace registry declares no {signal}"));
        pokes.get(slot).copied().unwrap_or(0)
    };
    ExitCounts {
        do_exit: count("DO_EXIT_FREE_SITE"),
        stmt_temp: count("STMT_TEMP_FREE_SITE"),
        root_exit: count("ROOT_EXIT_FREE_SITE"),
        ret_path: count("RET_PATH_FREE_SITE"),
        cond_temp: count("COND_TEMP_FREE_SITE"),
        arm_temp: count("ARM_TEMP_FREE_SITE"),
        ret_keep: count("RET_KEEP_FREE_SITE"),
        arm_split: count("JOIN_ARM_SPLIT"),
        scalar_skip: count("DO_EXIT_SCALAR_SKIP"),
    }
}

/// The oracle's verdict on one program: whether it accepted the
/// compile, and its stderr without the `ALM_TRACE:` pokes — the lines
/// a diagnostic pin compares (L6_HARNESS.md §2: filter the trace
/// lines, gate on the exit status, then read the first line).
pub fn oracle_verdict(name: &str, text: &str) -> (bool, Vec<String>) {
    let OracleRun { out, scratch } = run_oracle(name, text);
    let _ = std::fs::remove_dir_all(&scratch);
    let stderr = String::from_utf8_lossy(&out.stderr);
    (
        out.status.success(),
        stderr
            .lines()
            .filter(|line| !line.starts_with("ALM_TRACE:"))
            .map(str::to_string)
            .collect(),
    )
}

/// alm's side of the oracle table (L6_HARNESS.md §3): what the facts
/// hold, per family, in the oracle's units — one key per poke for the
/// temp maps and the keep-temps. The oracle pokes `DO_EXIT_FREE_SITE`
/// once per free of every scope-death plan, the root drain's included;
/// `RET_PATH_FREE_SITE` once per free of the two plain edge lists, and
/// `RET_KEEP_FREE_SITE` once per keep-free and once per keep-temp key;
/// and `JOIN_ARM_SPLIT` once per arm-split entry across its four maps
/// (two live since L3).
pub fn count_exit_families(facts: &ShapeFacts) -> ExitCounts {
    ExitCounts {
        do_exit: (facts.root_exit_frees.len()
            + facts.do_exit_frees.values().map(Vec::len).sum::<usize>()) as u32,
        stmt_temp: facts.stmt_temp_frees.len() as u32,
        root_exit: facts.root_exit_frees.len() as u32,
        ret_path: (facts.ret_path_frees.values().map(Vec::len).sum::<usize>()
            + facts.break_path_frees.values().map(Vec::len).sum::<usize>())
            as u32,
        cond_temp: facts.cond_temp_frees.len() as u32,
        arm_temp: facts.arm_temp_frees.len() as u32,
        ret_keep: (facts
            .ret_path_keep_frees
            .values()
            .map(Vec::len)
            .sum::<usize>()
            + facts.ret_path_keep_temps.len()) as u32,
        arm_split: (facts
            .arm_do_exit_frees
            .values()
            .chain(facts.arm_free_sites.values())
            .chain(facts.arm_rebind_frees.values())
            .map(Vec::len)
            .sum::<usize>()
            + facts.arm_root_exit_frees.len()) as u32,
        scalar_skip: 0,
    }
}

/// The entry lines of one section of the rendered shape dump — the
/// indented children under its `name:` header, in dump order; empty
/// when the section is absent (a section prints only when it has an
/// entry). Facts are addressed through lines, never raw ids:
/// `NodeId`s are minted per parse, so two analyses of one source
/// compare under the dump.
pub fn section<'a>(dump: &'a str, name: &str) -> Vec<&'a str> {
    let header = format!("{name}:");
    dump.lines()
        .skip_while(|line| *line != header.as_str())
        .skip(1)
        .take_while(|line| line.starts_with(' '))
        .collect()
}

/// The L6 pins' driver: `front` → `build_context` → `shape::analyze`
/// at base 0 with no splice, the walk-pins lever on (mirror's
/// `analyze_with` default). The program must come out diagnostic-free
/// or the pin dies; the run takes the sweep's big-stack thread.
pub fn facts_of(source: &str) -> (Vec<Stmt>, ShapeFacts) {
    let source = source.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let surface = Surface::default();
            let src = SourceFile::new("pin.lua", source);
            let out = front(&src, &surface);
            assert!(
                out.diagnostics.is_empty(),
                "pin source must parse clean: {:?}",
                out.diagnostics
            );
            let ctx = build_context(&out.ast);
            let facts = alm::shape::analyze(&ctx, true, &surface);
            assert!(
                facts.diagnostics.is_empty(),
                "pin source must analyze clean: {:?}",
                facts.diagnostics
            );
            (out.ast, facts)
        })
        .expect("spawn pin thread")
        .join()
        .expect("pin thread panicked")
}

/// The refused program's driver (6.2's diagnostic pin): `facts_of`'s
/// run, keeping the diagnostics instead of refusing them. The exit
/// planners run on whatever the walk got through — a scope-exit claim
/// that refuses a later read is minted before it refuses, and
/// `analyze_stage` would drop both the facts and this path.
pub fn facts_with_diagnostics(source: &str) -> (Vec<Stmt>, ShapeFacts) {
    let source = source.to_string();
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let surface = Surface::default();
            let src = SourceFile::new("pin.lua", source);
            let out = front(&src, &surface);
            assert!(
                out.diagnostics.is_empty(),
                "pin source must parse clean: {:?}",
                out.diagnostics
            );
            let ctx = build_context(&out.ast);
            let facts = alm::shape::analyze(&ctx, true, &surface);
            (out.ast, facts)
        })
        .expect("spawn pin thread")
        .join()
        .expect("pin thread panicked")
}

/// The lease helper (L6_HARNESS.md §5). A known legacy defect is never
/// a passing pin of the buggy behaviour: `body` asserts the *correct*
/// behaviour and is expected to fail. A pass fails the run and names
/// the lease (`known_lease/<name>`, a namespace of its own) — a
/// passing `cargo test` is the only signal the next session acts on.
/// The analysis runs outside the body, so its panic is an ordinary
/// failure; the default panic hook is silenced only around the
/// expected one.
pub fn xfail(lease: &str, body: impl FnOnce() + std::panic::UnwindSafe) {
    let prev_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let failed = std::panic::catch_unwind(body).is_err();
    std::panic::set_hook(prev_hook);
    assert!(
        failed,
        "lease known_lease/{lease} passed — the defect is fixed: retire the \
         lease, add the corpus case that pins the fixed law, re-bless"
    );
}

/// The site a ctor was minted, for the pins that destructure a
/// statement to its ctor nodes by hand.
pub fn site_of(facts: &ShapeFacts, ctor: NodeId) -> usize {
    *facts
        .sites
        .get(&ctor)
        .unwrap_or_else(|| panic!("no site was minted for ctor {ctor:?}"))
}
