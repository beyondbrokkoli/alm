//! Shared corpus idioms for the L2+ harness legs (integration tests
//! include this via `mod common;`).

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
