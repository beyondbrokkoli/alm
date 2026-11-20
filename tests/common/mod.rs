//! Shared corpus idioms for the L2+ harness legs (integration tests
//! include this via `mod common;`). Each test crate compiles its own
//! copy, so a leg that needs half the helpers would dead-code the rest
//! — the allowance below is the module's, not any layer's.
#![allow(dead_code)]

use alm::pipeline::front;
use alm::source::SourceFile;
use alm::surface::{Flag, Surface};
use std::path::{Path, PathBuf};

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

/// The L3 analyze leg's driver: front + splice + walk with the
/// `walk_pins` lever, on a thread with the sweep's stack headroom. A
/// panic maps to `Stage::Panicked` exactly as mirror's catch_unwind
/// harness does.
pub fn analyze_with_lever(
    path: String,
    text: String,
    walk_pins: bool,
) -> Result<String, (alm::pipeline::Stage, String)> {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let surface = surface_flags_of(&text);
            let src = SourceFile::new(path, text);
            let root = module_root();
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                alm::pipeline::analyze_stage(&src, &surface, Some(&root), walk_pins)
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
