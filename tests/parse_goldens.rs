//! L2 harness leg (REBASE_PLAN.md §4, §3.3.2): parse goldens. Every
//! corpus file the front end ACCEPTS gets a committed golden of its
//! post-desugar AST dump (`alm --dump-ast` output, surface flags
//! honored), freezing the parse contract: later layers (L3's require
//! splice first) port against these, and drift shows up as a diff, not
//! a hunch. Front-refusal files are excluded — their contract is the
//! byte-exact parity leg in front_parity.rs.
//!
//! Regen/bless: `ALM_BLESS=1 cargo test --test parse_goldens` writes
//! missing/drifted goldens; a bare run compares.

mod common;

use alm::dump::render_ast;
use common::{cases_dir, collect_lua_files, is_front_refusal, parse_on_big_stack};
use std::collections::BTreeSet;
use std::path::PathBuf;

fn goldens_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/goldens/ast")
}

/// The AST variant-coverage golden: the frozen corpus's accepted files
/// exercise exactly this set of node kinds (one — `SysExecCount` — has
/// no corpus case; the hand fixture below covers it, so the set stays
/// honest). The census rides the dump text (every node line begins
/// with its variant name), so no second walker exists to rot: a
/// grammar change surfaces as a diff against the frozen set, never as
/// silence.
const EXPECTED_KINDS: &[&str] = &[
    "Assignment",
    "AsyncModule",
    "BinaryOp",
    "Boolean",
    "Break",
    "Call",
    "Do",
    "ExprStmt",
    "FfiModule",
    "Field",
    "Float",
    "Function",
    "Identifier",
    "If",
    "Index",
    "IndexAssign",
    "Integer",
    "LocalDecl",
    "Nil",
    "Print",
    "Return",
    "String",
    "SysAllocCount",
    "TableCtor",
    "UnaryOp",
    "While",
];

#[test]
fn corpus_parse_goldens_freeze_the_l2_ast() {
    let root = cases_dir();
    let mut files = Vec::new();
    collect_lua_files(&root, &mut files);
    files.sort();
    assert!(
        files.len() >= 440,
        "corpus shrank to {} files — the frozen corpus of record is 449",
        files.len(),
    );

    let bless = std::env::var("ALM_BLESS").is_ok();
    let mut kinds: BTreeSet<String> = BTreeSet::new();
    let mut written = 0usize;
    let mut missing: Vec<String> = Vec::new();
    let mut drifted: Vec<String> = Vec::new();

    for path in &files {
        let name = path.file_name().unwrap().to_string_lossy().to_string();
        let text = std::fs::read_to_string(path).unwrap();
        let out = parse_on_big_stack(path.clone(), text);
        if !out.diagnostics.is_empty() {
            assert!(
                is_front_refusal(&name),
                "{name}: refusing outside the frozen catalog (see front_parity)"
            );
            continue;
        }
        let dump = render_ast(&out.ast);

        // Variant census over the dump: each node line's first token,
        // when it starts a kind name.
        for line in dump.lines() {
            if let Some(token) = line.split_whitespace().next()
                && token.starts_with(char::is_uppercase)
            {
                kinds.insert(token.to_string());
            }
        }

        let rel = path.strip_prefix(&root).expect("under corpus root");
        let golden = goldens_root().join(format!("{}.txt", rel.display()));
        if bless {
            let current = std::fs::read_to_string(&golden).ok();
            if current.as_deref() != Some(dump.as_str()) {
                std::fs::create_dir_all(golden.parent().expect("golden dir")).unwrap();
                std::fs::write(&golden, &dump).unwrap();
                written += 1;
            }
        } else {
            match std::fs::read_to_string(&golden) {
                Err(_) => missing.push(name),
                Ok(g) if g != dump => drifted.push(name),
                Ok(_) => {}
            }
        }
    }

    if bless {
        eprintln!(
            "bless: wrote {written} golden(s) under tests/goldens/ast/ — \
             re-run without ALM_BLESS to compare"
        );
    } else {
        assert!(
            missing.is_empty(),
            "{} golden(s) missing — run ALM_BLESS=1 cargo test --test parse_goldens: {}",
            missing.len(),
            missing.join(", ")
        );
        assert!(
            drifted.is_empty(),
            "{} golden(s) drifted — the parse contract moved; inspect with \
             alm --dump-ast, then bless if intended: {}",
            drifted.len(),
            drifted.join(", ")
        );
    }

    let expected: BTreeSet<String> = EXPECTED_KINDS.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        kinds, expected,
        "AST variant coverage over the corpus changed"
    );

    // The one variant the corpus leaves unexercised: `sys_exec_count()`
    // parses to `SysExecCount` (its sibling `sys_alloc_count` has
    // corpus cases; this counter has none yet).
    let exec_fixture = parse_on_big_stack(
        PathBuf::from("hand_fixture.lua"),
        "local n = sys_exec_count()\n".to_string(),
    );
    assert!(exec_fixture.is_ok(), "{:?}", exec_fixture.diagnostics);
    assert_eq!(
        render_ast(&exec_fixture.ast),
        "LocalDecl @1\n  names: n\n  SysExecCount\n"
    );
}
