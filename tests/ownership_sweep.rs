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
use alm::shape::{DoExitFree, Keep, ShapeFacts, is_ghost};
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

/// The seven exit-fate families the organ mints once 6.2 has landed,
/// in dump order: the scope-death planner's four around the temp
/// planner's three. A family's dump header is its name with dashes.
const FAMILIES: [&str; 7] = [
    "do_exit_frees",
    "root_exit_frees",
    "stmt_temp_frees",
    "cond_temp_frees",
    "arm_temp_frees",
    "arm_do_exit_frees",
    "arm_root_exit_frees",
];

fn temp_maps(facts: &ShapeFacts) -> [&BTreeMap<NodeId, Vec<usize>>; 3] {
    [
        &facts.stmt_temp_frees,
        &facts.cond_temp_frees,
        &facts.arm_temp_frees,
    ]
}

/// The seven families as a rendered dump carries them — the form two
/// analyses of one source compare under: raw `NodeId`s are minted per
/// parse, lines are not.
fn exit_sections(dump: &str) -> Vec<String> {
    FAMILIES
        .iter()
        .map(|family| section(dump, &family.replace('_', "-")).join("\n"))
        .collect()
}

/// The key spaces the exit planners mint into.
#[derive(Default)]
struct KeySpace {
    /// Print / Expr / LocalDecl / Assignment / IndexAssign — the
    /// statements `plan_stmt_temp_frees` scans for a temp.
    value_stmts: BTreeSet<NodeId>,
    /// While / If — the statements that own a condition.
    cond_stmts: BTreeSet<NodeId>,
    and_or_operands: BTreeSet<NodeId>,
    /// Every control statement's scope: `(stmt, 0)` for a While's
    /// body and a Do's block, `(stmt, 0)` and `(stmt, 1)` for an If's
    /// two arms — the keys `decide_scope_exit` mints at scope death.
    scope_keys: BTreeSet<(NodeId, u8)>,
    /// A statement's line, for the laws' messages.
    lines: BTreeMap<NodeId, u32>,
}

impl Visitor for KeySpace {
    type Break = Infallible;

    fn enter_stmt(&mut self, stmt: &Stmt) -> Result<(), Self::Break> {
        let id = stmt.id();
        self.lines.insert(id, stmt.loc().line);
        match stmt {
            Stmt::Print { .. }
            | Stmt::Expr { .. }
            | Stmt::LocalDecl { .. }
            | Stmt::Assignment { .. }
            | Stmt::IndexAssign { .. } => {
                self.value_stmts.insert(id);
            }
            Stmt::While { .. } => {
                self.cond_stmts.insert(id);
                self.scope_keys.insert((id, 0));
            }
            Stmt::If { .. } => {
                self.cond_stmts.insert(id);
                self.scope_keys.insert((id, 0));
                self.scope_keys.insert((id, 1));
            }
            Stmt::Do { .. } => {
                self.scope_keys.insert((id, 0));
            }
            Stmt::Return { .. } | Stmt::Break { .. } => {}
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

/// Every kept ghost is a minted row ghost.
fn check_keeps(name: &str, family: &str, keeps: &[Keep]) {
    for k in keeps {
        if let Keep::Ghost(g) = k {
            assert!(
                is_ghost(g),
                "{name}: {family} keeps ghost {g} — no row ghost was minted there"
            );
        }
    }
}

/// The laws of one scope-death free list: every freed site is a
/// minted ctor site or a row ghost, and no site frees twice under one
/// carrier. The list is planned per dying binding —
/// `compute_scope_frees` batches one entry per name — and two
/// bindings can own one ctor site (a call's returned record read under
/// two names, a table re-bound to a second name), so the same site may
/// appear again under another carrier; the census counts those.
fn check_frees(
    name: &str,
    family: &str,
    entry: &str,
    sites: &BTreeSet<usize>,
    frees: &[DoExitFree],
) {
    let mut seen: BTreeSet<(&str, usize)> = BTreeSet::new();
    for f in frees {
        assert!(
            sites.contains(&f.site) || is_ghost(&f.site),
            "{name}: {family}{entry} frees site {} — no ctor was minted there and no row \
             ghost is",
            f.site
        );
        assert!(
            seen.insert((f.carrier.as_str(), f.site)),
            "{name}: {family}{entry} frees site {} twice under the carrier '{}'",
            f.site,
            f.carrier
        );
        check_keeps(name, family, &f.keeps);
    }
}

/// The structural laws of the seven families, as far as they are
/// minted: a freed site is a minted ctor site (or, for the scope-death
/// maps, a row ghost); no site frees twice under one temp key or one
/// scope-death carrier; every kept ghost is a ghost. A temp key is the
/// statement its planner scans — a value statement for stmt temps, a
/// While / If for cond temps — or, for arm temps, an `and`/`or`
/// operand's expression. A do-exit key is a control statement's scope
/// — `(stmt, 0)` for a While or Do, `(stmt, 0)` or `(stmt, 1)` for an
/// If — or a fn literal's own scope key, as `fn_scope_keys` records
/// it.
fn check_laws(name: &str, ast: &[Stmt], facts: &ShapeFacts) {
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

    for (key, frees) in &facts.do_exit_frees {
        check_frees(
            name,
            "do_exit_frees",
            &format!(" under scope key {key:?}"),
            &sites,
            frees,
        );
    }
    check_frees(name, "root_exit_frees", "", &sites, &facts.root_exit_frees);
    for e in facts.arm_do_exit_frees.values().flatten() {
        check_keeps(name, "arm_do_exit_frees", &e.keeps);
    }
    for e in &facts.arm_root_exit_frees {
        check_keeps(name, "arm_root_exit_frees", &e.keeps);
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
    let fn_keys: BTreeSet<(NodeId, u8)> = facts.fn_scope_keys.values().copied().collect();
    for (stmt, k) in facts
        .do_exit_frees
        .keys()
        .chain(facts.arm_do_exit_frees.keys())
    {
        assert!(
            keys.scope_keys.contains(&(*stmt, *k)) || fn_keys.contains(&(*stmt, *k)),
            "{name}: a do-exit key is neither a control statement's scope nor a fn \
             literal's: (line {:?}, arm {k})",
            keys.lines.get(stmt)
        );
    }
}

/// What the sweep measured over the accepted corpus. Per family, in
/// `FAMILIES` order: the files carrying the family, and its entries —
/// frees for the two exit lists, keys for the temp maps, arm entries
/// for the two arm lists.
#[derive(Default)]
struct Census {
    files: [usize; 7],
    entries: [usize; 7],
    /// The sites freed — the three temp maps' and the two exit
    /// lists' (a row ghost's id counts as its site); zero for the arm
    /// lists, which free by tag and keep names.
    sites: [usize; 7],
    /// The do-exit map's scope keys — `decide_scope_exit` inserts its
    /// key even when nothing frees — how many of them are empty, and
    /// how many are a fn literal's body scope (the fn-body site's).
    scope_keys: usize,
    empty_scopes: usize,
    fn_scopes: usize,
    /// Exit frees (do-exit and root) carrying at least one keep.
    kept: usize,
    /// Frees of a site another carrier also frees in the same list —
    /// two bindings owning one ctor site — and the files holding them.
    shared: usize,
    shared_files: usize,
}

impl Census {
    fn add(&mut self, facts: &ShapeFacts) {
        let do_exit: usize = facts.do_exit_frees.values().map(Vec::len).sum();
        let [stmt, cond, arm] = temp_maps(facts);
        let arm_do_exit: usize = facts.arm_do_exit_frees.values().map(Vec::len).sum();
        let per_family = [
            (do_exit, do_exit),
            (facts.root_exit_frees.len(), facts.root_exit_frees.len()),
            (stmt.len(), stmt.values().map(Vec::len).sum()),
            (cond.len(), cond.values().map(Vec::len).sum()),
            (arm.len(), arm.values().map(Vec::len).sum()),
            (arm_do_exit, 0),
            (facts.arm_root_exit_frees.len(), 0),
        ];
        for (i, (entries, sites)) in per_family.into_iter().enumerate() {
            self.files[i] += usize::from(entries > 0);
            self.entries[i] += entries;
            self.sites[i] += sites;
        }
        self.scope_keys += facts.do_exit_frees.len();
        self.empty_scopes += facts
            .do_exit_frees
            .values()
            .filter(|f| f.is_empty())
            .count();
        let fn_keys: BTreeSet<(NodeId, u8)> = facts.fn_scope_keys.values().copied().collect();
        self.fn_scopes += facts
            .do_exit_frees
            .keys()
            .filter(|key| fn_keys.contains(key))
            .count();
        self.kept += facts
            .do_exit_frees
            .values()
            .flatten()
            .chain(&facts.root_exit_frees)
            .filter(|f| !f.keeps.is_empty())
            .count();
        let lists = facts
            .do_exit_frees
            .values()
            .chain(std::iter::once(&facts.root_exit_frees));
        let shared: usize = lists
            .map(|frees| {
                let distinct: BTreeSet<usize> = frees.iter().map(|f| f.site).collect();
                frees.len() - distinct.len()
            })
            .sum();
        self.shared += shared;
        self.shared_files += usize::from(shared > 0);
    }

    fn print(&self) {
        for (i, family) in FAMILIES.iter().enumerate() {
            let unit = match i {
                0 | 1 => "frees",
                2..=4 => "entries",
                _ => "arm entries",
            };
            eprintln!(
                "  {family}: {} files, {} {unit}, {} sites freed",
                self.files[i], self.entries[i], self.sites[i]
            );
        }
        eprintln!(
            "  do-exit scope keys: {} ({} empty, {} fn bodies); exit frees carrying a keep: \
             {}; frees sharing a site with another carrier: {} in {} files",
            self.scope_keys,
            self.empty_scopes,
            self.fn_scopes,
            self.kept,
            self.shared,
            self.shared_files
        );
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
                check_laws(name, &ast, &facts);
                census.add(&facts);
                let Outcome::Accepted(_, _, again) = analyze(name.clone(), text.clone()) else {
                    panic!("{name}: the second analysis run did not accept the source")
                };
                assert_eq!(
                    exit_sections(&dump),
                    exit_sections(&again),
                    "{name}: the exit-fate families are not a pure function of the source"
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
    let mut oracle = ExitCounts::default();
    let mut alm = ExitCounts::default();
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
                // Equal, family by family: the cond and arm temps, and
                // the root drain — each is planned once per program.
                assert_eq!(
                    mine.cond_temp, plate.cond_temp,
                    "{name}: cond-temp keys vs the oracle's pokes"
                );
                assert_eq!(
                    mine.arm_temp, plate.arm_temp,
                    "{name}: arm-temp keys vs the oracle's pokes"
                );
                assert_eq!(
                    mine.root_exit, plate.root_exit,
                    "{name}: root-exit frees vs the oracle's pokes"
                );
                // At most, family by family. The stmt temps gain their
                // scalar-return branch at 6.3. A do-exit free and an
                // arm-split entry are poked once per planning call, and
                // the While arm's latch loop can walk a body more than
                // once in the recorded pass while the maps keep one
                // entry — so alm may sit below, never above.
                assert!(
                    mine.stmt_temp <= plate.stmt_temp,
                    "{name}: {} stmt-temp keys, but the oracle poked {}",
                    mine.stmt_temp,
                    plate.stmt_temp
                );
                assert!(
                    mine.do_exit <= plate.do_exit,
                    "{name}: {} do-exit frees (the root drain included), but the oracle \
                     poked {}",
                    mine.do_exit,
                    plate.do_exit
                );
                assert!(
                    mine.arm_split <= plate.arm_split,
                    "{name}: {} arm-split entries, but the oracle poked {}",
                    mine.arm_split,
                    plate.arm_split
                );
                oracle = oracle.add(plate);
                alm = alm.add(mine);
            }
        }
    }
    eprintln!(
        "oracle plate over {analyzed} accepted files ({refused} refused): \
         do-exit {} / {}, stmt {} / {}, root {} / {}, cond {} / {}, arm {} / {}, \
         arm-split {} / {} (oracle / alm)",
        oracle.do_exit,
        alm.do_exit,
        oracle.stmt_temp,
        alm.stmt_temp,
        oracle.root_exit,
        alm.root_exit,
        oracle.cond_temp,
        alm.cond_temp,
        oracle.arm_temp,
        alm.arm_temp,
        oracle.arm_split,
        alm.arm_split
    );
    assert!(
        panics.is_empty(),
        "the exit-fate planner panicked on {} corpus file(s): {}",
        panics.len(),
        panics.join(", ")
    );
    // The oracle's own totals are the pre-registered ones
    // (L6_HARNESS.md §3, the accepted-corpus column). Anything else is
    // the harness — flags, module root, a wrapped plate — never the
    // port.
    assert_eq!(
        oracle,
        ExitCounts {
            do_exit: 397,
            stmt_temp: 19,
            root_exit: 226,
            ret_path: 10,
            cond_temp: 2,
            arm_temp: 4,
            ret_keep: 35,
            arm_split: 2,
            scalar_skip: 10,
        },
        "the oracle's own totals over the files alm accepts"
    );
    assert_eq!(alm.cond_temp, 2, "cond-temp entries over the corpus");
    assert_eq!(alm.arm_temp, 4, "arm-temp entries over the corpus");
    assert!(
        alm.stmt_temp <= 19,
        "{} stmt-temp entries over the corpus — at most the oracle's 19 until 6.3",
        alm.stmt_temp
    );
    // Equal: the root drain runs once per program, and no accepted
    // corpus case plans an arm split from a latched loop body.
    assert_eq!(alm.root_exit, 226, "root-exit frees over the corpus");
    assert_eq!(alm.arm_split, 2, "arm-split entries over the corpus");
    assert!(
        alm.do_exit <= 397,
        "{} do-exit frees over the corpus — at most the oracle's 397",
        alm.do_exit
    );
}
