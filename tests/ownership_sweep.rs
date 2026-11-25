//! The ownership corpus sweep (L6's leg — L6_DESIGN.md §7): over the
//! whole corpus the exit-fate families obey their structural laws,
//! are a pure function of the source, never panic, and count what the
//! frozen oracle's own trace plate says it minted (L6_HARNESS.md
//! §3–§4). mirror's leg diffs emitted IR; that oracle is L7's, so the
//! plate counts the facts until then, and the pins
//! (`ownership_pins.rs`) hold the contents the plate cannot see.
//!
//! The oracle-plate reader's own pin rides first; it was green before
//! the organ existed. The census thresholds froze at 6.3, with the
//! organ whole: lower bounds on what that run measured
//! (`Census::check_frozen`).

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

/// The four site-list maps in family order: the temp-fate planner's
/// three — statement, condition, and/or operand — and the return
/// edge's keep-temps, a table-typed return's ctor bases. One law covers
/// the four: every site a minted ctor, no site twice under one key.
const TEMP_FAMILIES: [&str; 4] = [
    "stmt_temp_frees",
    "cond_temp_frees",
    "arm_temp_frees",
    "ret_path_keep_temps",
];

/// The three edge lists keyed by their own statement, in dump order.
const EDGE_LISTS: [&str; 3] = ["ret_path_frees", "break_path_frees", "ret_path_keep_frees"];

/// The eleven exit-fate families the whole organ mints, in dump order:
/// the scope-death planner's four around the temp planner's three and
/// the edge planners' four. A family's dump header is its name with
/// dashes.
const FAMILIES: [&str; 11] = [
    "do_exit_frees",
    "root_exit_frees",
    "stmt_temp_frees",
    "cond_temp_frees",
    "arm_temp_frees",
    "ret_path_frees",
    "break_path_frees",
    "ret_path_keep_frees",
    "ret_path_keep_temps",
    "arm_do_exit_frees",
    "arm_root_exit_frees",
];

fn temp_maps(facts: &ShapeFacts) -> [&BTreeMap<NodeId, Vec<usize>>; 4] {
    [
        &facts.stmt_temp_frees,
        &facts.cond_temp_frees,
        &facts.arm_temp_frees,
        &facts.ret_path_keep_temps,
    ]
}

fn edge_maps(facts: &ShapeFacts) -> [&BTreeMap<NodeId, Vec<DoExitFree>>; 3] {
    [
        &facts.ret_path_frees,
        &facts.break_path_frees,
        &facts.ret_path_keep_frees,
    ]
}

/// The eleven families as a rendered dump carries them — the form two
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
    /// The edge statements, the keys the two edge planners mint: a
    /// return (the return lists and the keep-temps; the scalar-return
    /// stmt temps too) and a break.
    returns: BTreeSet<NodeId>,
    breaks: BTreeSet<NodeId>,
    /// The returns outside every fn literal — the boundary, where the
    /// return edge clears its keeps: `fn_scope_entries` is empty
    /// exactly while no fn body is being walked, and a fn body is
    /// walked only from its literal.
    boundary_returns: BTreeSet<NodeId>,
    /// Whether the walk is inside a fn literal's body.
    in_fn: bool,
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
            Stmt::Return { .. } => {
                self.returns.insert(id);
                if !self.in_fn {
                    self.boundary_returns.insert(id);
                }
            }
            Stmt::Break { .. } => {
                self.breaks.insert(id);
            }
        }
        Ok(())
    }

    fn visit_function(
        &mut self,
        _params: &[String],
        body: &[Stmt],
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        let outer = std::mem::replace(&mut self.in_fn, true);
        let walked = walk_stmts(self, body);
        self.in_fn = outer;
        walked
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

/// The laws of one scope-death or edge free list: every freed site is
/// a minted ctor site or a row ghost, and no site frees twice under one
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

/// The structural laws of the eleven families, as far as they are
/// minted: a freed site is a minted ctor site (or, for the scope-death
/// and edge lists, a row ghost); no site frees twice under one temp key
/// or one list carrier; every kept ghost is a ghost. A temp key is the
/// statement its planner scans — a value statement for stmt temps, or
/// a return, whose scalar value mints stmt temps of its own from
/// `plan_return_exits` — a While / If for cond temps, and for arm
/// temps an `and`/`or` operand's expression. An edge list is keyed by
/// its own statement — a return for the two return lists and the
/// keep-temps, a break for the break list — and a return outside every
/// fn literal is the boundary: its keeps are cleared, because the host
/// owns the artifact's exit. A do-exit key is a control statement's
/// scope — `(stmt, 0)` for a While or Do, `(stmt, 0)` or `(stmt, 1)`
/// for an If — or a fn literal's own scope key, as `fn_scope_keys`
/// records it.
///
/// Answers how many edge lists are keyed by a boundary return — the
/// boundary law's witnesses, for the census.
fn check_laws(name: &str, ast: &[Stmt], facts: &ShapeFacts) -> usize {
    let sites: BTreeSet<usize> = facts.sites.values().copied().collect();
    for (family, frees) in TEMP_FAMILIES.iter().zip(temp_maps(facts)) {
        for list in frees.values() {
            for site in list {
                assert!(
                    sites.contains(site),
                    "{name}: {family} lists site {site} — no ctor was minted there"
                );
            }
            let distinct: BTreeSet<usize> = list.iter().copied().collect();
            assert_eq!(
                distinct.len(),
                list.len(),
                "{name}: {family} lists one site twice under a key"
            );
        }
    }

    let mut keys = KeySpace::default();
    let _ = walk_stmts(&mut keys, ast);
    let at = |stmt: &NodeId| format!(" at line {:?}", keys.lines.get(stmt));

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
    let mut boundary = 0;
    for (family, list) in EDGE_LISTS.iter().zip(edge_maps(facts)) {
        for (stmt, frees) in list {
            check_frees(name, family, &at(stmt), &sites, frees);
            if keys.boundary_returns.contains(stmt) {
                boundary += 1;
                assert!(
                    frees.iter().all(|f| f.keeps.is_empty()),
                    "{name}: {family}{} keeps a name or a ghost — a return with no fn \
                     entry clears its keeps (the host owns the artifact's exit)",
                    at(stmt)
                );
            }
        }
    }
    for e in facts.arm_do_exit_frees.values().flatten() {
        check_keeps(name, "arm_do_exit_frees", &e.keeps);
    }
    for e in &facts.arm_root_exit_frees {
        check_keeps(name, "arm_root_exit_frees", &e.keeps);
    }

    let [stmt, cond, arm, keep_temps] = temp_maps(facts);
    for key in stmt.keys() {
        assert!(
            keys.value_stmts.contains(key) || keys.returns.contains(key),
            "{name}: a stmt-temp key is neither a Print / Expr / LocalDecl / Assignment / \
             IndexAssign statement nor a return"
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
    for key in keep_temps.keys() {
        assert!(
            keys.returns.contains(key),
            "{name}: a keep-temp key is not a return statement"
        );
    }
    for key in facts
        .ret_path_frees
        .keys()
        .chain(facts.ret_path_keep_frees.keys())
    {
        assert!(
            keys.returns.contains(key),
            "{name}: a return-edge key is not a return statement"
        );
    }
    for key in facts.break_path_frees.keys() {
        assert!(
            keys.breaks.contains(key),
            "{name}: a break-path key is not a break statement"
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
    boundary
}

/// The keeps of a list by kind: `(names, ghosts)`.
fn count_keeps<'a>(keeps: impl IntoIterator<Item = &'a Keep>) -> (usize, usize) {
    let mut names = 0;
    let mut ghosts = 0;
    for k in keeps {
        match k {
            Keep::Name(_) => names += 1,
            Keep::Ghost(_) => ghosts += 1,
        }
    }
    (names, ghosts)
}

/// What the sweep measured over the accepted corpus. Per family, in
/// `FAMILIES` order: the files carrying the family, and its entries —
/// frees for the five exit lists, keys for the temp maps and the
/// keep-temps, arm entries for the two arm lists.
#[derive(Default)]
struct Census {
    files: [usize; 11],
    entries: [usize; 11],
    /// The sites the lists free — the temp maps' and the exit lists'
    /// (a row ghost's id counts as its site), the keep-temps' kept;
    /// zero for the arm lists, which free by tag and keep names.
    sites: [usize; 11],
    /// The do-exit map's scope keys — `decide_scope_exit` inserts its
    /// key even when nothing frees — how many of them are empty, and
    /// how many are a fn literal's body scope (the fn-body site's).
    scope_keys: usize,
    empty_scopes: usize,
    fn_scopes: usize,
    /// Exit frees (do-exit and root) carrying at least one keep.
    kept: usize,
    /// Edge frees (the three edge lists) carrying at least one keep.
    edge_kept: usize,
    /// Edge lists keyed by a return at the boundary — outside every fn
    /// literal — and the files holding them: the census of the boundary
    /// law.
    boundary_keys: usize,
    boundary_files: usize,
    /// The arm-split entries as the oracle counts them: the joint of
    /// four maps, two live since L3.
    arm_split: usize,
    /// Frees of a site another carrier also frees in the same list —
    /// two bindings owning one ctor site — and the files holding them.
    shared: usize,
    shared_files: usize,
    /// The keeps themselves, by kind: over the five exit lists
    /// (do-exit, root and the three edge lists) and over the four arm
    /// lists.
    exit_name_keeps: usize,
    exit_ghost_keeps: usize,
    arm_name_keeps: usize,
    arm_ghost_keeps: usize,
}

impl Census {
    fn add(&mut self, facts: &ShapeFacts) {
        let do_exit: usize = facts.do_exit_frees.values().map(Vec::len).sum();
        let [stmt, cond, arm, keep_temps] = temp_maps(facts);
        let arm_do_exit: usize = facts.arm_do_exit_frees.values().map(Vec::len).sum();
        let edge: [usize; 3] = edge_maps(facts).map(|list| list.values().map(Vec::len).sum());
        let per_family = [
            (do_exit, do_exit),
            (facts.root_exit_frees.len(), facts.root_exit_frees.len()),
            (stmt.len(), stmt.values().map(Vec::len).sum()),
            (cond.len(), cond.values().map(Vec::len).sum()),
            (arm.len(), arm.values().map(Vec::len).sum()),
            (edge[0], edge[0]),
            (edge[1], edge[1]),
            (edge[2], edge[2]),
            (keep_temps.len(), keep_temps.values().map(Vec::len).sum()),
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
        self.edge_kept += edge_maps(facts)
            .into_iter()
            .flat_map(|list| list.values().flatten())
            .filter(|f| !f.keeps.is_empty())
            .count();
        self.arm_split += count_exit_families(facts).arm_split as usize;
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
        let (names, ghosts) = count_keeps(
            facts
                .do_exit_frees
                .values()
                .flatten()
                .chain(&facts.root_exit_frees)
                .chain(
                    edge_maps(facts)
                        .into_iter()
                        .flat_map(|list| list.values().flatten()),
                )
                .flat_map(|f| f.keeps.iter()),
        );
        self.exit_name_keeps += names;
        self.exit_ghost_keeps += ghosts;
        let (names, ghosts) = count_keeps(
            facts
                .arm_do_exit_frees
                .values()
                .flatten()
                .chain(&facts.arm_root_exit_frees)
                .chain(facts.arm_free_sites.values().flatten())
                .chain(facts.arm_rebind_frees.values().flatten())
                .flat_map(|e| e.keeps.iter()),
        );
        self.arm_name_keeps += names;
        self.arm_ghost_keeps += ghosts;
    }

    fn print(&self) {
        for (i, family) in FAMILIES.iter().enumerate() {
            let unit = match i {
                0 | 1 | 5..=7 => "frees",
                2..=4 | 8 => "entries",
                _ => "arm entries",
            };
            let freed = if i == 8 { "sites kept" } else { "sites freed" };
            eprintln!(
                "  {family}: {} files, {} {unit}, {} {freed}",
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
        eprintln!(
            "  sums: do-exit {} + root {} = {}; ret/break-path {}; temp entries {} (stmt {}, \
             cond {}, arm {}); arm-split entries {} (the joint of four maps; {} in the two \
             scope-death lists)",
            self.entries[0],
            self.entries[1],
            self.entries[0] + self.entries[1],
            self.entries[5] + self.entries[6],
            self.entries[2] + self.entries[3] + self.entries[4],
            self.entries[2],
            self.entries[3],
            self.entries[4],
            self.arm_split,
            self.entries[9] + self.entries[10]
        );
        eprintln!(
            "  keeps: {} Name, {} Ghost over the five exit lists; {} Name, {} Ghost over the \
             four arm lists; edge frees carrying a keep: {}; edge lists keyed at the \
             boundary: {} in {} files",
            self.exit_name_keeps,
            self.exit_ghost_keeps,
            self.arm_name_keeps,
            self.arm_ghost_keeps,
            self.edge_kept,
            self.boundary_keys,
            self.boundary_files
        );
    }

    /// The census frozen at 6.3 (L6_DESIGN.md §6), when the organ
    /// became whole: lower bounds on what that run measured over the
    /// accepted corpus. The oracle's plate states the six equal-relation
    /// families exactly and the other leg asserts them; these floors
    /// cover what the plate cannot see — a family losing its witnesses
    /// to a later port, or the accepted pool shrinking.
    fn check_frozen(&self, analyzed: usize) {
        let temp_entries = self.entries[2] + self.entries[3] + self.entries[4];
        let floors = [
            ("analyzed files", analyzed, 325),
            ("do-exit frees", self.entries[0], 171),
            ("root frees", self.entries[1], 226),
            (
                "ret/break-path frees",
                self.entries[5] + self.entries[6],
                10,
            ),
            ("temp entries (stmt + cond + arm)", temp_entries, 25),
            ("arm-split entries", self.arm_split, 2),
            ("Name keeps over the exit lists", self.exit_name_keeps, 1),
            ("Ghost keeps over the exit lists", self.exit_ghost_keeps, 1),
        ];
        for (what, measured, frozen) in floors {
            assert!(
                measured >= frozen,
                "the ownership census fell below the floor frozen at 6.3: {measured} {what} \
                 (frozen: {frozen})"
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
                let boundary = check_laws(name, &ast, &facts);
                census.boundary_keys += boundary;
                census.boundary_files += usize::from(boundary > 0);
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
    census.check_frozen(analyzed);
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
                // Equal, family by family — each is planned once per
                // program: the cond and arm temps, the stmt temps (the
                // scalar-return branch landed at 6.3), the root drain,
                // and both edge families.
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
                assert_eq!(
                    mine.stmt_temp, plate.stmt_temp,
                    "{name}: {} stmt-temp keys, but the oracle poked {}",
                    mine.stmt_temp, plate.stmt_temp
                );
                assert_eq!(
                    mine.ret_path, plate.ret_path,
                    "{name}: {} ret/break-path frees, but the oracle poked {}",
                    mine.ret_path, plate.ret_path
                );
                assert_eq!(
                    mine.ret_keep, plate.ret_keep,
                    "{name}: {} ret-keep frees and keys, but the oracle poked {}",
                    mine.ret_keep, plate.ret_keep
                );
                // At most, family by family. A do-exit free and an
                // arm-split entry are poked once per planning call, and
                // the While arm's latch loop can walk a body more than
                // once in the recorded pass while the maps keep one
                // entry — so alm may sit below, never above.
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
         do-exit {} / {}, stmt {} / {}, root {} / {}, ret/break-path {} / {}, cond {} / {}, \
         arm {} / {}, ret-keep {} / {}, arm-split {} / {} (oracle / alm)",
        oracle.do_exit,
        alm.do_exit,
        oracle.stmt_temp,
        alm.stmt_temp,
        oracle.root_exit,
        alm.root_exit,
        oracle.ret_path,
        alm.ret_path,
        oracle.cond_temp,
        alm.cond_temp,
        oracle.arm_temp,
        alm.arm_temp,
        oracle.ret_keep,
        alm.ret_keep,
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
    // The six equal-relation families, exactly the oracle's numbers
    // (frozen at 6.3, L6_DESIGN.md §6): each is planned once per
    // program over the accepted corpus, so no accepted case re-plans
    // one of their entries under a key that already holds it.
    assert_eq!(alm.stmt_temp, 19, "stmt-temp entries over the corpus");
    assert_eq!(alm.cond_temp, 2, "cond-temp entries over the corpus");
    assert_eq!(alm.arm_temp, 4, "arm-temp entries over the corpus");
    assert_eq!(alm.root_exit, 226, "root-exit frees over the corpus");
    assert_eq!(alm.ret_path, 10, "ret/break-path frees over the corpus");
    assert_eq!(alm.ret_keep, 35, "ret-keep frees and keys over the corpus");
    // At most by relation — a latched loop body re-plans under one key
    // — and equal as measured (6.2).
    assert_eq!(alm.arm_split, 2, "arm-split entries over the corpus");
    assert!(
        alm.do_exit <= 397,
        "{} do-exit frees over the corpus — at most the oracle's 397",
        alm.do_exit
    );
}
