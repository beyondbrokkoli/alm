//! The ownership corpus sweep (L6's leg — L6_DESIGN.md §7): over the
//! whole corpus the exit-fate families obey their structural laws,
//! are a pure function of the source, never panic, and count what the
//! frozen oracle's own trace plate says it minted (L6_HARNESS.md
//! §3–§4). mirror's leg diffs emitted IR; that oracle is L7's, so the
//! plate counts the facts until then, and the pins
//! (`ownership_pins.rs`) hold the contents the plate cannot see.
//!
//! The oracle-plate reader's own pin rides first; it was green before
//! the organ existed.

mod common;

use alm::ast::{BinOp, Expr, NodeId, Stmt};
use alm::pipeline::analyze_stage;
use alm::shape::ShapeFacts;
use alm::source::SourceFile;
use alm::visit::{Visitor, walk_expr, walk_stmts};
use common::{
    ExitCounts, cases_dir, collect_lua_files, count_exit_families, module_root, oracle_exit_counts,
    section, standalone_of, surface_flags_of,
};
use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;

#[test]
fn oracle_plate_reader_agrees_with_known_counts() {
    // Measured from the oracle's plate by hand at pre-flight: whole
    // rows, so a slot read under the wrong name cannot hide behind a
    // family the table leaves blank. (The third row's do-exit poke is
    // the root chunk's own batch — 6.2 mints it.)
    let rows = [
        (
            "30_pin_cond_arm_temps.lua",
            ExitCounts {
                cond_temp: 2,
                arm_temp: 4,
                ..ExitCounts::default()
            },
        ),
        (
            "24_pin_ctor_temp_lifetime.lua",
            ExitCounts {
                stmt_temp: 3,
                ..ExitCounts::default()
            },
        ),
        (
            "25_pin_root_scope_exit.lua",
            ExitCounts {
                do_exit: 1,
                stmt_temp: 1,
                root_exit: 1,
                ret_keep: 1,
                ..ExitCounts::default()
            },
        ),
    ];
    for (name, want) in rows {
        let text = std::fs::read_to_string(cases_dir().join(name))
            .unwrap_or_else(|e| panic!("{name} unreadable: {e}"));
        assert_eq!(
            oracle_exit_counts(name, &text),
            want,
            "{name}: the plate reader disagrees with the oracle"
        );
    }
}

/// One corpus file's verdict: on acceptance the spliced AST, its
/// facts (boxed — they cross a `Result` and dwarf the other variants),
/// and the facts as rendered. A panic is its own outcome, never folded
/// into a rejection: the planner runs on refused programs too, so a
/// crash there is this leg's to count.
enum Outcome {
    Accepted(Vec<Stmt>, Box<ShapeFacts>, String),
    Refused,
    Panicked,
}

/// One corpus file through the canonical path (front → splice → walk +
/// checker → gate), the way the oracle compiles it: the case's FLAGS
/// and link mode, the module root, the walk-pins lever on. The run
/// takes a 64 MiB thread under its own `catch_unwind`.
fn analyze(name: String, text: String) -> Outcome {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let surface = surface_flags_of(&text);
                let standalone = standalone_of(&text);
                let src = SourceFile::new(name, text);
                let root = module_root();
                analyze_stage(&src, &surface, Some(&root), true, standalone).map(|out| {
                    let dump = alm::dump::render_shape(&out.facts, &out.ast);
                    (out.ast, out.facts, dump)
                })
            }));
            match run {
                Ok(Ok((ast, facts, dump))) => Outcome::Accepted(ast, Box::new(facts), dump),
                Ok(Err((_stage, _diags))) => Outcome::Refused,
                Err(_) => Outcome::Panicked,
            }
        })
        .expect("spawn sweep thread")
        .join()
        .unwrap_or(Outcome::Panicked)
}

/// The corpus as `(name, text)` — the path under the cases root,
/// `/`-separated, which is the oracle helper's name for a corpus file.
fn corpus() -> Vec<(String, String)> {
    let root = cases_dir();
    let mut files = Vec::new();
    collect_lua_files(&root, &mut files);
    files.sort();
    files
        .into_iter()
        .map(|path| {
            let name = path
                .strip_prefix(&root)
                .expect("a collected case lives under the corpus root")
                .to_string_lossy()
                .replace('\\', "/");
            let text = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("{} unreadable: {e}", path.display()));
            (name, text)
        })
        .collect()
}

/// The three temp-fate maps in family order: statement, condition,
/// and/or operand.
const TEMP_FAMILIES: [&str; 3] = ["stmt_temp_frees", "cond_temp_frees", "arm_temp_frees"];

fn temp_maps(facts: &ShapeFacts) -> [&BTreeMap<NodeId, Vec<usize>>; 3] {
    [
        &facts.stmt_temp_frees,
        &facts.cond_temp_frees,
        &facts.arm_temp_frees,
    ]
}

/// The three temp families as a rendered dump carries them — the form
/// two analyses of one source compare under: raw `NodeId`s are minted
/// per parse, lines are not. (A family's dump header is its name with
/// dashes.)
fn temp_sections(dump: &str) -> Vec<String> {
    TEMP_FAMILIES
        .iter()
        .map(|family| section(dump, &family.replace('_', "-")).join("\n"))
        .collect()
}

/// The key spaces the temp planner mints into: every statement's kind
/// and every `and`/`or` operand's expression id.
#[derive(Default)]
struct KeySpace {
    /// Print / Expr / LocalDecl / Assignment / IndexAssign — the
    /// statements `plan_stmt_temp_frees` scans for a temp.
    value_stmts: BTreeSet<NodeId>,
    /// While / If — the statements that own a condition.
    cond_stmts: BTreeSet<NodeId>,
    and_or_operands: BTreeSet<NodeId>,
}

impl Visitor for KeySpace {
    type Break = Infallible;

    fn enter_stmt(&mut self, stmt: &Stmt) -> Result<(), Self::Break> {
        match stmt {
            Stmt::Print { .. }
            | Stmt::Expr { .. }
            | Stmt::LocalDecl { .. }
            | Stmt::Assignment { .. }
            | Stmt::IndexAssign { .. } => {
                self.value_stmts.insert(stmt.id());
            }
            Stmt::While { .. } | Stmt::If { .. } => {
                self.cond_stmts.insert(stmt.id());
            }
            Stmt::Do { .. } | Stmt::Return { .. } | Stmt::Break { .. } => {}
        }
        Ok(())
    }

    fn visit_binary_op(
        &mut self,
        op: &BinOp,
        left: &Expr,
        right: &Expr,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        if matches!(op, BinOp::And | BinOp::Or) {
            self.and_or_operands.insert(left.id());
            self.and_or_operands.insert(right.id());
        }
        walk_expr(self, left)?;
        walk_expr(self, right)
    }
}

/// The structural laws of the three temp maps, as far as 6.1 mints
/// them: every freed site is a minted ctor site; no site frees twice
/// under one key; a key is the statement its planner scans — a value
/// statement for stmt temps, a While / If for cond temps — or, for arm
/// temps, an `and`/`or` operand's expression.
fn check_temp_laws(name: &str, ast: &[Stmt], facts: &ShapeFacts) {
    let sites: BTreeSet<usize> = facts.sites.values().copied().collect();
    for (family, frees) in TEMP_FAMILIES.iter().zip(temp_maps(facts)) {
        for list in frees.values() {
            for site in list {
                assert!(
                    sites.contains(site),
                    "{name}: {family} frees site {site} — no ctor was minted there"
                );
            }
            let distinct: BTreeSet<usize> = list.iter().copied().collect();
            assert_eq!(
                distinct.len(),
                list.len(),
                "{name}: {family} frees one site twice under a key"
            );
        }
    }
    let mut keys = KeySpace::default();
    let _ = walk_stmts(&mut keys, ast);
    let [stmt, cond, arm] = temp_maps(facts);
    for key in stmt.keys() {
        assert!(
            keys.value_stmts.contains(key),
            "{name}: a stmt-temp key is not a Print / Expr / LocalDecl / Assignment / \
             IndexAssign statement"
        );
    }
    for key in cond.keys() {
        assert!(
            keys.cond_stmts.contains(key),
            "{name}: a cond-temp key is not a While / If statement"
        );
    }
    for key in arm.keys() {
        assert!(
            keys.and_or_operands.contains(key),
            "{name}: an arm-temp key is not an and/or operand"
        );
    }
}

/// What the sweep measured over the accepted corpus: per temp family,
/// the files carrying it, its entries (keys) and the sites they free.
#[derive(Default)]
struct Census {
    files: [usize; 3],
    entries: [usize; 3],
    sites: [usize; 3],
}

impl Census {
    fn add(&mut self, facts: &ShapeFacts) {
        for (i, frees) in temp_maps(facts).into_iter().enumerate() {
            self.files[i] += usize::from(!frees.is_empty());
            self.entries[i] += frees.len();
            self.sites[i] += frees.values().map(Vec::len).sum::<usize>();
        }
    }

    fn print(&self) {
        for (i, family) in TEMP_FAMILIES.iter().enumerate() {
            eprintln!(
                "  {family}: {} files, {} entries, {} sites freed",
                self.files[i], self.entries[i], self.sites[i]
            );
        }
    }
}

#[test]
fn ownership_corpus_sweep() {
    let corpus = corpus();
    assert!(
        corpus.len() >= 449,
        "the corpus pool shrank: {}",
        corpus.len()
    );

    let mut analyzed = 0usize;
    let mut refused = 0usize;
    let mut panics: Vec<String> = Vec::new();
    let mut census = Census::default();
    for (name, text) in &corpus {
        match analyze(name.clone(), text.clone()) {
            Outcome::Panicked => panics.push(name.clone()),
            Outcome::Refused => refused += 1,
            Outcome::Accepted(ast, facts, dump) => {
                analyzed += 1;
                check_temp_laws(name, &ast, &facts);
                census.add(&facts);
                let Outcome::Accepted(_, _, again) = analyze(name.clone(), text.clone()) else {
                    panic!("{name}: the second analysis run did not accept the source")
                };
                assert_eq!(
                    temp_sections(&dump),
                    temp_sections(&again),
                    "{name}: the temp-fate families are not a pure function of the source"
                );
            }
        }
    }
    eprintln!(
        "ownership census: {analyzed} analyzed / {refused} refused of {}; panics {}",
        corpus.len(),
        panics.len()
    );
    census.print();
    assert!(
        panics.is_empty(),
        "the exit-fate planner panicked on {} corpus file(s): {}",
        panics.len(),
        panics.join(", ")
    );
}

#[test]
fn ownership_facts_match_the_oracle() {
    let corpus = corpus();
    assert!(
        corpus.len() >= 449,
        "the corpus pool shrank: {}",
        corpus.len()
    );

    let mut analyzed = 0usize;
    let mut refused = 0usize;
    let mut panics: Vec<String> = Vec::new();
    // Per temp family, over the accepted corpus: the oracle's pokes
    // and alm's entries.
    let mut oracle = [0u32; 3];
    let mut alm = [0u32; 3];
    for (name, text) in &corpus {
        match analyze(name.clone(), text.clone()) {
            Outcome::Panicked => panics.push(name.clone()),
            Outcome::Refused => refused += 1,
            Outcome::Accepted(_, facts, _) => {
                analyzed += 1;
                let mine = count_exit_families(&facts);
                // A refused program mints pokes too, but
                // `analyze_stage` drops its facts — accepted files
                // are the ones that compare.
                let plate = oracle_exit_counts(name, text);
                assert_eq!(
                    mine.cond_temp, plate.cond_temp,
                    "{name}: cond-temp keys vs the oracle's pokes"
                );
                assert_eq!(
                    mine.arm_temp, plate.arm_temp,
                    "{name}: arm-temp keys vs the oracle's pokes"
                );
                // At most: the scalar-return branch that also writes a
                // stmt temp lands at 6.3.
                assert!(
                    mine.stmt_temp <= plate.stmt_temp,
                    "{name}: {} stmt-temp keys, but the oracle poked {}",
                    mine.stmt_temp,
                    plate.stmt_temp
                );
                oracle[0] += plate.stmt_temp;
                oracle[1] += plate.cond_temp;
                oracle[2] += plate.arm_temp;
                alm[0] += mine.stmt_temp;
                alm[1] += mine.cond_temp;
                alm[2] += mine.arm_temp;
            }
        }
    }
    eprintln!(
        "oracle plate over {analyzed} accepted files ({refused} refused): \
         stmt {} / {}, cond {} / {}, arm {} / {}",
        oracle[0], alm[0], oracle[1], alm[1], oracle[2], alm[2]
    );
    assert!(
        panics.is_empty(),
        "the exit-fate planner panicked on {} corpus file(s): {}",
        panics.len(),
        panics.join(", ")
    );
    // The oracle's own totals are the pre-registered ones
    // (L6_HARNESS.md §3: 13 files / 19 pokes, 1 / 2, 1 / 4 over the
    // accepted corpus). Anything else is the harness — flags, module
    // root, a wrapped plate — never the port.
    assert_eq!(
        oracle,
        [19, 2, 4],
        "the oracle's own totals over the files alm accepts"
    );
    assert_eq!(alm[1], 2, "cond-temp entries over the corpus");
    assert_eq!(alm[2], 4, "arm-temp entries over the corpus");
    assert!(
        alm[0] <= 19,
        "{} stmt-temp entries over the corpus — at most the oracle's 19 until 6.3",
        alm[0]
    );
}
