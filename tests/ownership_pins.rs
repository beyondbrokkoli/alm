//! The exit-fate pins (L6_DESIGN.md §6): the hand-written programs of
//! `L6_PORT_MAP.md` §7, each asserting what the organ's law says —
//! derived from its code, never from a run — and carrying the oracle's
//! own count for its source (L6_HARNESS.md §3). The temp-fate programs
//! (T1–T9, 6.1) and the scope-death and root-drain programs (S1–S9,
//! 6.2). Facts are addressed through the rendered dump: a section by
//! name, a statement by line, a ctor site by the line it was born on —
//! never a raw id. Where two ctors share a line (T9, L1 and its
//! control) the pin destructures the statement to the ctor nodes
//! instead.
//!
//! The one lease, `known_lease/field-obj-arm-scan`, asserts the
//! correct behaviour under `common::xfail`: it must fail until the
//! chartered fix, and a pass fails the run.

mod common;

use alm::ast::{BinOp, Expr, NodeId, Stmt};
use alm::shape::ShapeFacts;
use common::{
    analyze_with_lever, count_exit_families, oracle_exit_counts, oracle_verdict, section, site_of,
    xfail,
};

const T1: &str = "local f = function() return {1, 2} end\n\
                  print(f()[0])\n\
                  print(({3, 4})[0])\n\
                  local g = function(x) print(x[0]) end\n\
                  g({9, 8})\n";

const T2: &str = "local t = {1, 2}\n\
                  local u = {3}\n\
                  t = {4}\n\
                  print(t[0] + u[0])\n";

const T3: &str = "local flag = ({1})[0]\n\
                  print(flag)\n";

const T4: &str = "print(#{10, 20})\n\
                  local a = {}\n\
                  print(a == {})\n";

const T5: &str = "local carrier = {{9}}\n\
                  local mv = function(x) carrier[1] = x end\n\
                  mv({7, 8})\n\
                  local br = function(x) return x end\n\
                  br({5})\n\
                  local st = function(t) t[9] = 1 end\n\
                  st({})\n";

const T6: &str = "print(({1})[0] == 1 and ({2})[0] == 2)\n\
                  print(({1})[0] == 9 or ({2})[0] == 2)\n";

const T7: &str = "if ({1})[0] == 1 then print(9) end\n\
                  local i = 0\n\
                  while ({5})[i] == 5 do i = i + 1 end\n";

const T8: &str = "local outer = function()\n\
                  \x20   local inner = function()\n\
                  \x20       print(({7})[0])\n\
                  \x20   end\n\
                  \x20   inner()\n\
                  \x20   print(({8})[0])\n\
                  end\n";

const T9: &str = "print({{1}} == {{2}})\n";

/// The leased shape: the record hangs off a `Field`'s obj.
const L1: &str = "local r = ({ n = 1 == 1 and ({1})[0] == 1 }).n\n\
                  print(r)\n";

/// The same record bound directly — the lease's control.
const L1_CONTROL: &str = "local r = { n = 1 == 1 and ({1})[0] == 1 }\n\
                          print(r.n)\n";

/// One entry line of a temp-frees section — `  @line L sites [a b]`
/// — as `(line, freed sites)`.
fn temp_entries(dump: &str, name: &str) -> Vec<(u32, Vec<usize>)> {
    section(dump, name)
        .iter()
        .map(|line| {
            let (at, list) = line
                .trim()
                .strip_prefix("@line ")
                .and_then(|rest| rest.split_once(" sites ["))
                .unwrap_or_else(|| panic!("not a temp-frees entry: {line:?}"));
            let list = list
                .strip_suffix(']')
                .unwrap_or_else(|| panic!("the entry's site list closes: {line:?}"));
            let sites = if list.is_empty() {
                Vec::new()
            } else {
                list.split(' ')
                    .map(|s| s.parse().expect("a site id"))
                    .collect()
            };
            (at.parse().expect("a line number"), sites)
        })
        .collect()
}

/// The lines carrying an entry in a temp-frees section, in dump order.
fn temp_lines(dump: &str, name: &str) -> Vec<u32> {
    temp_entries(dump, name)
        .iter()
        .map(|(line, _)| *line)
        .collect()
}

/// The sites freed under the one entry at `line`.
fn temp_sites_at(dump: &str, name: &str, line: u32) -> Vec<usize> {
    let mut at: Vec<Vec<usize>> = temp_entries(dump, name)
        .into_iter()
        .filter(|(at, _)| *at == line)
        .map(|(_, sites)| sites)
        .collect();
    assert_eq!(
        at.len(),
        1,
        "exactly one {name} entry sits at line {line}:\n{}",
        section(dump, name).join("\n")
    );
    at.remove(0)
}

/// Every site whose ctor was born at `line` — the `  site N @line L`
/// rows — in site order.
fn sites_born_at(dump: &str, line: u32) -> Vec<usize> {
    dump.lines()
        .filter_map(|row| {
            let (site, rest) = row.strip_prefix("  site ")?.split_once(" @line ")?;
            let born = rest.split_once(' ')?.0;
            (born.parse::<u32>() == Ok(line)).then(|| site.parse().expect("a site id"))
        })
        .collect()
}

/// The site born at `line`, where the program keeps one ctor per line.
fn site_born_at(dump: &str, line: u32) -> usize {
    let mut born = sites_born_at(dump, line);
    assert_eq!(born.len(), 1, "exactly one ctor is born at line {line}");
    born.remove(0)
}

/// The right operand of the record's `and`, and the ctor it indexes:
/// the arm key the law wants, and the site it must free. Both L1
/// programs hold the same record.
fn leased_arm(record: &Expr) -> (NodeId, NodeId) {
    let Expr::TableCtor { entries, .. } = record else {
        panic!("the program builds one record ctor");
    };
    let Expr::BinaryOp {
        op: BinOp::And,
        right,
        ..
    } = &entries[0].1
    else {
        panic!("the record's field is an `and`");
    };
    let Expr::BinaryOp { left, .. } = right.as_ref() else {
        panic!("the right operand is a comparison");
    };
    let Expr::Index { obj, .. } = left.as_ref() else {
        panic!("the comparison's left side is an index");
    };
    (right.id(), obj.id())
}

#[test]
fn t1_stmt_temp_index_base() {
    let (ast, facts) = common::facts_of(T1);
    let dump = alm::dump::render_shape(&facts, &ast);
    // Print / Expr statements scan with `Dies`, and the Index arm
    // always rescans obj and key with `Dies`: line 2 frees the ctor
    // the inlined `f` returns (born on line 1), lines 3 and 5 the ctor
    // each indexes or passes read-only. The two bindings' fn literals
    // plan no temp of their own.
    assert_eq!(temp_lines(&dump, "stmt-temp-frees"), [2, 3, 5]);
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 2),
        [site_born_at(&dump, 1)]
    );
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 3),
        [site_born_at(&dump, 3)]
    );
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 5),
        [site_born_at(&dump, 5)]
    );
    assert!(section(&dump, "cond-temp-frees").is_empty());
    assert!(section(&dump, "arm-temp-frees").is_empty());
    assert_eq!(
        oracle_exit_counts("t1_stmt_temp_index_base.lua", T1).stmt_temp,
        3
    );
}

#[test]
fn t2_ctor_escapes_into_binding() {
    let (ast, facts) = common::facts_of(T2);
    let dump = alm::dump::render_shape(&facts, &ast);
    // LocalDecl and Assignment scan with `Escapes`: a ctor that lands
    // in a binding is the binding's to free at root exit (6.2), never
    // a temp.
    assert!(section(&dump, "stmt-temp-frees").is_empty());
    assert!(section(&dump, "cond-temp-frees").is_empty());
    assert!(section(&dump, "arm-temp-frees").is_empty());
    assert_eq!(
        oracle_exit_counts("t2_ctor_escapes_into_binding.lua", T2).stmt_temp,
        0
    );
}

#[test]
fn t3_index_base_scans_as_dies() {
    let (ast, facts) = common::facts_of(T3);
    let dump = alm::dump::render_shape(&facts, &ast);
    // The Index arm hands its obj `Dies` whatever fate the statement
    // was scanned with — here `Escapes`, because the value lands in a
    // binding. Reading the binding back frees nothing.
    assert_eq!(temp_lines(&dump, "stmt-temp-frees"), [1]);
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 1),
        [site_born_at(&dump, 1)]
    );
    assert!(section(&dump, "cond-temp-frees").is_empty());
    assert!(section(&dump, "arm-temp-frees").is_empty());
    assert_eq!(
        oracle_exit_counts("t3_index_base_scans_as_dies.lua", T3).stmt_temp,
        1
    );
}

#[test]
fn t4_len_and_binary_operands() {
    let (ast, facts) = common::facts_of(T4);
    let dump = alm::dump::render_shape(&facts, &ast);
    // A unary operand and a comparison's two sides scan with `Dies`:
    // the ctor under `#` dies with the length, the one compared
    // against `a` with the comparison. `a`'s own ctor escapes.
    assert_eq!(temp_lines(&dump, "stmt-temp-frees"), [1, 3]);
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 1),
        [site_born_at(&dump, 1)]
    );
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 3),
        [site_born_at(&dump, 3)]
    );
    assert!(section(&dump, "cond-temp-frees").is_empty());
    assert!(section(&dump, "arm-temp-frees").is_empty());
    assert_eq!(
        oracle_exit_counts("t4_len_and_binary_operands.lua", T4).stmt_temp,
        2
    );
}

#[test]
fn t5_call_arg_fates() {
    let (ast, facts) = common::facts_of(T5);
    let dump = alm::dump::render_shape(&facts, &ast);
    // A call argument takes the callee's parameter fate: `mv`'s
    // parameter moves, so line 3 frees nothing; `br` returns its
    // parameter and the argument is not a bare name — `Dies`; `st`'s
    // parameter is plain — `Dies`.
    assert_eq!(temp_lines(&dump, "stmt-temp-frees"), [5, 7]);
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 5),
        [site_born_at(&dump, 5)]
    );
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 7),
        [site_born_at(&dump, 7)]
    );
    assert!(section(&dump, "cond-temp-frees").is_empty());
    assert!(section(&dump, "arm-temp-frees").is_empty());
    assert_eq!(oracle_exit_counts("t5_call_arg_fates.lua", T5).stmt_temp, 2);
}

#[test]
fn t6_and_or_arm_law() {
    let (ast, facts) = common::facts_of(T6);
    let dump = alm::dump::render_shape(&facts, &ast);
    // The statement scan never descends an `and`/`or`; the arm planner
    // keys each operand by its own expression — two per line here —
    // and frees the operand's ctor.
    assert!(section(&dump, "stmt-temp-frees").is_empty());
    let arms = temp_entries(&dump, "arm-temp-frees");
    let lines: Vec<u32> = arms.iter().map(|(line, _)| *line).collect();
    assert_eq!(lines, [1, 1, 2, 2]);
    for (line, sites) in &arms {
        assert_eq!(sites.len(), 1, "one site per operand — its own ctor");
        assert!(
            sites_born_at(&dump, *line).contains(&sites[0]),
            "line {line}'s operand frees a ctor born on that line"
        );
    }
    let mut freed: Vec<usize> = arms
        .iter()
        .flat_map(|(_, sites)| sites.iter().copied())
        .collect();
    freed.sort_unstable();
    freed.dedup();
    assert_eq!(freed.len(), 4, "the four operands free four distinct ctors");
    let oracle = oracle_exit_counts("t6_and_or_arm_law.lua", T6);
    assert_eq!(oracle.arm_temp, 4);
    assert_eq!(oracle.stmt_temp, 0);
}

#[test]
fn t7_cond_temps() {
    let (ast, facts) = common::facts_of(T7);
    let dump = alm::dump::render_shape(&facts, &ast);
    // A condition frees its temps where its value is consumed: the If
    // and the While are each keyed by their own statement. The branch
    // body and the loop body plan nothing.
    assert_eq!(temp_lines(&dump, "cond-temp-frees"), [1, 3]);
    assert_eq!(
        temp_sites_at(&dump, "cond-temp-frees", 1),
        [site_born_at(&dump, 1)]
    );
    assert_eq!(
        temp_sites_at(&dump, "cond-temp-frees", 3),
        [site_born_at(&dump, 3)]
    );
    assert!(section(&dump, "stmt-temp-frees").is_empty());
    assert!(section(&dump, "arm-temp-frees").is_empty());
    let oracle = oracle_exit_counts("t7_cond_temps.lua", T7);
    assert_eq!(oracle.cond_temp, 2);
    assert_eq!(oracle.stmt_temp, 0);
}

#[test]
fn t8_fn_bodies_replan_recursively() {
    let (ast, facts) = common::facts_of(T8);
    let dump = alm::dump::render_shape(&facts, &ast);
    // A fn literal's body is re-planned recursively, so the nested
    // literal's print (line 3) and the outer body's (line 6) each free
    // the ctor they index.
    assert_eq!(temp_lines(&dump, "stmt-temp-frees"), [3, 6]);
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 3),
        [site_born_at(&dump, 3)]
    );
    assert_eq!(
        temp_sites_at(&dump, "stmt-temp-frees", 6),
        [site_born_at(&dump, 6)]
    );
    assert!(section(&dump, "cond-temp-frees").is_empty());
    assert!(section(&dump, "arm-temp-frees").is_empty());
    assert_eq!(
        oracle_exit_counts("t8_fn_bodies_replan_recursively.lua", T8).stmt_temp,
        2
    );
}

#[test]
fn t9_deepfree_pruning() {
    let (ast, facts) = common::facts_of(T9);
    let dump = alm::dump::render_shape(&facts, &ast);
    // Two ctors share the line, so the sites come from the nodes. Both
    // operands scan with `Dies` and collect all four ctors — the outer
    // ones and the rows they hold; prune_deepfree_children then drops
    // every site another collected site deep-frees.
    assert_eq!(temp_lines(&dump, "stmt-temp-frees"), [1]);
    let Stmt::Print { exprs, .. } = &ast[0] else {
        panic!("the program is one print")
    };
    let Expr::BinaryOp { left, right, .. } = &exprs[0] else {
        panic!("it prints a comparison of two ctors")
    };
    fn row(side: &Expr) -> &Expr {
        match side {
            Expr::TableCtor { entries, .. } if entries.len() == 1 => &entries[0].1,
            _ => panic!("each side is a ctor holding one row"),
        }
    }
    let (outer_l, outer_r) = (left.as_ref(), right.as_ref());
    let (inner_l, inner_r) = (row(outer_l), row(outer_r));
    assert_eq!(
        facts.stmt_temp_frees.len(),
        1,
        "one key — the print statement"
    );
    let freed = facts
        .stmt_temp_frees
        .get(&ast[0].id())
        .expect("the print statement frees its temps");
    assert_eq!(freed.len(), 2, "exactly the two outer ctors survive");
    assert!(freed.contains(&site_of(&facts, outer_l.id())));
    assert!(freed.contains(&site_of(&facts, outer_r.id())));
    assert!(
        !freed.contains(&site_of(&facts, inner_l.id())),
        "the left row dies with its parent's deep free"
    );
    assert!(
        !freed.contains(&site_of(&facts, inner_r.id())),
        "the right row dies with its parent's deep free"
    );
    assert!(section(&dump, "cond-temp-frees").is_empty());
    assert!(section(&dump, "arm-temp-frees").is_empty());
    assert_eq!(
        oracle_exit_counts("t9_deepfree_pruning.lua", T9).stmt_temp,
        1
    );
}

/// The sites an expression's arm entry frees — `None` when no entry
/// is keyed there.
fn arm_frees(facts: &ShapeFacts, operand: NodeId) -> Option<&[usize]> {
    facts.arm_temp_frees.get(&operand).map(Vec::as_slice)
}

#[test]
fn l1_control_arm_temp_under_record_ctor() {
    let (ast, facts) = common::facts_of(L1_CONTROL);
    let Stmt::LocalDecl { exprs, .. } = &ast[0] else {
        panic!("the program is one local declaration")
    };
    let (operand, ctor) = leased_arm(&exprs[0]);
    // The record escapes into the binding — no stmt temp — and the
    // `and` under its field is still arm-scanned: the right operand is
    // keyed, freeing the ctor it indexes.
    assert!(facts.stmt_temp_frees.is_empty());
    assert_eq!(
        arm_frees(&facts, operand),
        Some(&[site_of(&facts, ctor)][..])
    );
    assert_eq!(facts.arm_temp_frees.len(), 1);
    assert!(facts.cond_temp_frees.is_empty());
    let oracle = oracle_exit_counts("l1_control_arm_temp_under_record_ctor.lua", L1_CONTROL);
    assert_eq!(oracle.arm_temp, 1);
    assert_eq!(oracle.stmt_temp, 0);
}

#[test]
fn l1_lease_field_obj_arm_scan() {
    // The analysis and the oracle's count run outside the lease, so a
    // panic there is an ordinary failure.
    let (ast, facts) = common::facts_of(L1);
    let Stmt::LocalDecl { exprs, .. } = &ast[0] else {
        panic!("the program is one local declaration")
    };
    let Expr::Field { obj, .. } = &exprs[0] else {
        panic!("the initializer reads a field off a record ctor")
    };
    // The Field arm hands its obj `Dies`: the record itself is a stmt
    // temp of the declaration.
    let record = [site_of(&facts, obj.id())];
    assert_eq!(
        facts.stmt_temp_frees.get(&ast[0].id()).map(Vec::as_slice),
        Some(&record[..])
    );
    assert_eq!(facts.stmt_temp_frees.len(), 1);
    assert!(facts.cond_temp_frees.is_empty());
    // (The oracle's arm count here is the bug's own number — it is
    // deliberately not asserted.)
    assert_eq!(
        oracle_exit_counts("l1_field_obj_arm_scan.lua", L1).stmt_temp,
        1
    );
    let (operand, ctor) = leased_arm(obj);
    let site = [site_of(&facts, ctor)];
    xfail("field-obj-arm-scan", || {
        assert_eq!(
            arm_frees(&facts, operand),
            Some(&site[..]),
            "the right operand of the `and` is arm-keyed, freeing its ctor's site"
        );
    });
}

// — 6.2: scope death and the root drain (`L6_PORT_MAP.md` §7). The
// programs keep their own line numbers: the pins name statements by
// line.

const S1: &str = "do
    local t = {}
    t[0] = 1
    print(t[0])
end
";

const S2: &str = "local i = 0
while i < 2 do
    local t = {}
    t[0] = i
    print(t[0])
    i = i + 1
end
";

const S3: &str = "if 1 < 2 then
    local t = {}
    t[0] = 1
    print(t[0])
end
";

const S4: &str = "local t = {5, 6}
local u = {7}
print(t[0] + u[0])
";

/// S5 with a second read of the row after its housing died.
const S6: &str = "local a = {{1, 2}, {3}}
do
    local t = {}
    t[0] = a[0]
    print(t[0][0])
end
print(a[0][0])
";

const S8: &str = "do
    local mix_base = {{9, 8}, {7}}
    local mix
    if 1 == 1 then mix = {99} else mix = mix_base[0] end
    print(mix[0])
end
";

const S9: &str = "local mix_base = {{9, 8}, {7}}
local mix
if 1 == 1 then mix = {99} else mix = mix_base[0] end
print(mix[0])
";

/// S5 on its own: the first five lines of S6.
const S5: &str = "local a = {{1, 2}, {3}}
do
    local t = {}
    t[0] = a[0]
    print(t[0][0])
end
";

/// One exit free as the dump renders it: the carrier, the site it
/// frees — a ctor site or a row ghost, printed raw — and its keeps.
#[derive(Debug, PartialEq)]
struct Freed {
    site: usize,
    carrier: String,
    keeps: Vec<String>,
}

/// One arm-split free as the dump renders it. `at` is the scope key —
/// the owning statement's line and its arm — on a do-exit entry, and
/// `None` on the root drain's.
#[derive(Debug, PartialEq)]
struct ArmSplit {
    at: Option<(u32, u8)>,
    carrier: String,
    tag: String,
    nothing_on: bool,
    keeps: Vec<String>,
}

/// An entry line split at its `keeps:` field: what precedes it, and
/// the keeps as rendered (names, `ghost N`) — empty when none.
fn keeps_field(line: &str) -> (&str, Vec<String>) {
    let (head, keeps) = line
        .trim()
        .rsplit_once("keeps:")
        .unwrap_or_else(|| panic!("not an exit-fate entry: {line:?}"));
    let keeps = keeps.trim();
    (
        head.trim_end(),
        if keeps.is_empty() {
            Vec::new()
        } else {
            keeps.split(", ").map(str::to_string).collect()
        },
    )
}

/// A do-exit entry — `  @line L arm K site S carrier keeps: …` — as
/// the scope's line, its arm, and the free.
fn do_exit_entry(line: &str) -> (u32, u8, Freed) {
    let (head, keeps) = keeps_field(line);
    let (scope, rest) = head
        .strip_prefix("@line ")
        .and_then(|rest| rest.split_once(" arm "))
        .unwrap_or_else(|| panic!("not a do-exit entry: {line:?}"));
    let (arm, rest) = rest.split_once(" site ").expect("the freed site");
    let (site, carrier) = rest.split_once(' ').expect("the carrier");
    (
        scope.parse().expect("a line number"),
        arm.parse().expect("an arm"),
        Freed {
            site: site.parse().expect("a site id"),
            carrier: carrier.to_string(),
            keeps,
        },
    )
}

/// A root-drain entry — `  site S carrier keeps: …`.
fn root_exit_entry(line: &str) -> Freed {
    let (head, keeps) = keeps_field(line);
    let (site, carrier) = head
        .strip_prefix("site ")
        .and_then(|rest| rest.split_once(' '))
        .unwrap_or_else(|| panic!("not a root-exit entry: {line:?}"));
    Freed {
        site: site.parse().expect("a site id"),
        carrier: carrier.to_string(),
        keeps,
    }
}

/// An arm-split entry — `[`@line L arm K `]carrier tag T
/// nothing_on=B keeps: …`: the scope key on a do-exit entry, none on
/// the root drain's.
fn arm_split_entry(line: &str) -> ArmSplit {
    let (head, keeps) = keeps_field(line);
    let (at, rest) = match head.strip_prefix("@line ") {
        Some(rest) => {
            let (scope, rest) = rest.split_once(" arm ").expect("the scope's arm");
            let (arm, rest) = rest.split_once(' ').expect("the carrier");
            (
                Some((
                    scope.parse().expect("a line number"),
                    arm.parse().expect("an arm"),
                )),
                rest,
            )
        }
        None => (None, head),
    };
    let (carrier, rest) = rest.split_once(" tag ").expect("the join's tag");
    let (tag, nothing_on) = rest.split_once(" nothing_on=").expect("nothing_on");
    ArmSplit {
        at,
        carrier: carrier.to_string(),
        tag: tag.to_string(),
        nothing_on: nothing_on.parse().expect("a bool"),
        keeps,
    }
}

/// The do-exit frees under the scope at `line`, arm `arm` — empty
/// when that scope frees nothing (its key then prints no line).
fn do_exit_at(dump: &str, line: u32, arm: u8) -> Vec<Freed> {
    section(dump, "do-exit-frees")
        .iter()
        .filter_map(|entry| do_exit_entry(entry).into())
        .filter(|(at, k, _)| *at == line && *k == arm)
        .map(|(_, _, f)| f)
        .collect()
}

/// The root drain's frees, in name order.
fn root_exit(dump: &str) -> Vec<Freed> {
    section(dump, "root-exit-frees")
        .iter()
        .map(|entry| root_exit_entry(entry))
        .collect()
}

/// The arm-split frees under the scope at `line`, arm `arm`.
fn arm_do_exit_at(dump: &str, line: u32, arm: u8) -> Vec<ArmSplit> {
    section(dump, "arm-do-exit-frees")
        .iter()
        .map(|entry| arm_split_entry(entry))
        .filter(|split| split.at == Some((line, arm)))
        .collect()
}

/// The root drain's arm-split frees.
fn arm_root(dump: &str) -> Vec<ArmSplit> {
    section(dump, "arm-root-exit-frees")
        .iter()
        .map(|entry| arm_split_entry(entry))
        .collect()
}

/// A `local x = <expr>` statement's initializer.
fn initializer(stmt: &Stmt) -> &Expr {
    let Stmt::LocalDecl { exprs, .. } = stmt else {
        panic!("the statement is a local declaration")
    };
    &exprs[0]
}

/// The row ghosts a store at `line` houses — its row of the
/// `store-ghost-keeps` section.
fn ghosts_housed_at(dump: &str, line: u32) -> Vec<usize> {
    section(dump, "store-ghost-keeps")
        .iter()
        .filter_map(|row| {
            let (at, list) = row.trim().strip_prefix("@line ")?.split_once(" ghosts [")?;
            (at.parse::<u32>() == Ok(line)).then(|| {
                list.strip_suffix(']')
                    .expect("the ghost list closes")
                    .split(' ')
                    .filter(|g| !g.is_empty())
                    .map(|g| g.parse().expect("a ghost id"))
                    .collect::<Vec<_>>()
            })
        })
        .flatten()
        .collect()
}

#[test]
fn s1_do_plain_free() {
    let (ast, facts) = common::facts_of(S1);
    let dump = alm::dump::render_shape(&facts, &ast);
    // A block's death plans its innermost scope — the Do's own — after
    // the body walk and before the pop: `t` dies there with its one
    // ctor, nothing kept. The root scope holds only `arg`, whose alias
    // is a root site and is filtered, so the drain frees nothing.
    assert!(
        matches!(&ast[0], Stmt::Do { .. }),
        "the program is one do block"
    );
    assert_eq!(facts.do_exit_frees.len(), 1, "one scope key — the block's");
    assert!(facts.do_exit_frees.contains_key(&(ast[0].id(), 0)));
    assert_eq!(
        do_exit_at(&dump, 1, 0),
        [Freed {
            site: site_born_at(&dump, 2),
            carrier: "t".into(),
            keeps: Vec::new(),
        }]
    );
    assert!(root_exit(&dump).is_empty());
    assert!(facts.root_exit_frees.is_empty());
    let oracle = oracle_exit_counts("s1_do_plain_free.lua", S1);
    assert_eq!((oracle.do_exit, oracle.root_exit), (1, 0));
    let mine = count_exit_families(&facts);
    assert_eq!((mine.do_exit, mine.root_exit), (1, 0));
}

#[test]
fn s2_while_body_scope_free() {
    let (ast, facts) = common::facts_of(S2);
    let dump = alm::dump::render_shape(&facts, &ast);
    // The While arm plans inside `with_scope`, on every trip of the
    // latch loop: each trip re-plans the body scope under the one key
    // `(While, 0)`, and the insert replaces, so one fact stands. `i`
    // is a value kind: the root drain skips it.
    assert!(matches!(&ast[1], Stmt::While { .. }));
    assert_eq!(
        facts.do_exit_frees.len(),
        1,
        "one scope key — the loop body's"
    );
    assert!(facts.do_exit_frees.contains_key(&(ast[1].id(), 0)));
    assert_eq!(
        do_exit_at(&dump, 2, 0),
        [Freed {
            site: site_born_at(&dump, 3),
            carrier: "t".into(),
            keeps: Vec::new(),
        }]
    );
    assert!(root_exit(&dump).is_empty());
    let oracle = oracle_exit_counts("s2_while_body_scope_free.lua", S2);
    assert_eq!((oracle.do_exit, oracle.root_exit), (1, 0));
    let mine = count_exit_families(&facts);
    assert_eq!((mine.do_exit, mine.root_exit), (1, 0));
}

#[test]
fn s3_if_arm_scope_free() {
    let (ast, facts) = common::facts_of(S3);
    let dump = alm::dump::render_shape(&facts, &ast);
    // Each arm is its own scope, planned as it closes: the then arm
    // (k = 0) frees `t`; the else arm (k = 1) owns nothing, and its key
    // still lands — with an empty list, which prints no line, so that
    // half reads off the map.
    assert!(matches!(&ast[0], Stmt::If { .. }));
    assert_eq!(
        do_exit_at(&dump, 1, 0),
        [Freed {
            site: site_born_at(&dump, 2),
            carrier: "t".into(),
            keeps: Vec::new(),
        }]
    );
    assert!(
        facts
            .do_exit_frees
            .get(&(ast[0].id(), 1))
            .is_some_and(|frees| frees.is_empty()),
        "the else arm's key lands with an empty list"
    );
    assert_eq!(
        facts.do_exit_frees.len(),
        2,
        "the then arm and the else arm"
    );
    assert!(root_exit(&dump).is_empty());
    let oracle = oracle_exit_counts("s3_if_arm_scope_free.lua", S3);
    assert_eq!((oracle.do_exit, oracle.root_exit), (1, 0));
    let mine = count_exit_families(&facts);
    assert_eq!((mine.do_exit, mine.root_exit), (1, 0));
}

#[test]
fn s4_root_drain() {
    let (ast, facts) = common::facts_of(S4);
    let dump = alm::dump::render_shape(&facts, &ast);
    // The root drain plans scope 0 once the walk is done: every
    // binding with a non-root alias frees, in name order (the dying
    // scope is a BTreeMap) — `t` then `u` — each with nothing kept. No
    // inner scope died on the way, so the do-exit map is empty.
    assert!(facts.do_exit_frees.is_empty());
    assert_eq!(
        root_exit(&dump),
        [
            Freed {
                site: site_born_at(&dump, 1),
                carrier: "t".into(),
                keeps: Vec::new(),
            },
            Freed {
                site: site_born_at(&dump, 2),
                carrier: "u".into(),
                keeps: Vec::new(),
            },
        ]
    );
    let oracle = oracle_exit_counts("s4_root_drain.lua", S4);
    assert_eq!((oracle.do_exit, oracle.root_exit), (2, 2));
    let mine = count_exit_families(&facts);
    assert_eq!((mine.do_exit, mine.root_exit), (2, 2));
}

#[test]
fn s5_housed_origin_defers_fire_with_keeps() {
    let (ast, facts) = common::facts_of(S5);
    let dump = alm::dump::render_shape(&facts, &ast);
    let Stmt::Do { body, .. } = &ast[1] else {
        panic!("the program ends in a do block")
    };
    let a = site_of(&facts, initializer(&ast[0]).id());
    let t = site_of(&facts, initializer(&body[0]).id());
    let [ghost] = ghosts_housed_at(&dump, 4)[..] else {
        panic!("the store on line 4 houses one row")
    };
    // The store `t[0] = a[0]` houses the row ghost in `t`: it links
    // the row's site into t's `row_links`; t's own aliases stay its one
    // ctor, so nothing is mixed and nothing defers.
    // `housed_in_release` answers two different sets. At the block's
    // death t's release finds the ghost's base in t's *housing*: the
    // ghost is claimed, not spared, and t's free carries no keep. At
    // the root drain a's release set holds the row's site while a
    // houses nothing: the same ghost is *spared*, and a's free carries
    // it as its one keep. The block frees `t` alone — `a` is a root
    // binding — and the drain frees `a`.
    assert_eq!(
        do_exit_at(&dump, 2, 0),
        [Freed {
            site: t,
            carrier: "t".into(),
            keeps: Vec::new(),
        }]
    );
    assert_eq!(facts.do_exit_frees.len(), 1);
    assert_eq!(
        root_exit(&dump),
        [Freed {
            site: a,
            carrier: "a".into(),
            keeps: vec![format!("ghost {ghost}")],
        }]
    );
    let oracle = oracle_exit_counts("s5_housed_origin_defers_fire_with_keeps.lua", S5);
    assert_eq!((oracle.do_exit, oracle.root_exit), (2, 1));
    let mine = count_exit_families(&facts);
    assert_eq!((mine.do_exit, mine.root_exit), (2, 1));
}

#[test]
fn s6_scope_exit_claim_read_refused() {
    // The refusal the claim buys: after the block dies, the row `a[0]`
    // was released with its housing `t` (S5's claim), so reading it
    // through `a` again is a read of a claimed ghost.
    const REFUSED: &str = "line 7: Lifetime Error: this row was already released with its \
                           housing — read it through the housing's cell before it drops";
    let (ast, facts) = common::facts_with_diagnostics(S6);
    let refusals: Vec<String> = facts.diagnostics.iter().map(|d| d.render()).collect();
    assert_eq!(refusals, [REFUSED], "S6 is refused, once, at the read");
    // The exit planners ran all the same — they ride the tail whatever
    // the walk's outcome: the block's free of `t` and the drain's of
    // `a`, as in S5.
    let dump = alm::dump::render_shape(&facts, &ast);
    let Stmt::Do { body, .. } = &ast[1] else {
        panic!("the program's second statement is the do block")
    };
    let t = site_of(&facts, initializer(&body[0]).id());
    assert_eq!(
        do_exit_at(&dump, 2, 0)
            .iter()
            .map(|f| (f.site, f.carrier.as_str(), f.keeps.is_empty()))
            .collect::<Vec<_>>(),
        [(t, "t", true)]
    );
    let root = root_exit(&dump);
    assert_eq!(root.len(), 1);
    assert_eq!(root[0].carrier, "a");
    assert_eq!(
        root[0].keeps.len(),
        1,
        "a's free spares the housed row ghost, as in S5"
    );
    // The canonical path (front → splice → walk + checker → gate)
    // refuses with the same line.
    match analyze_with_lever(
        "s6_scope_exit_claim_read_refused.lua".into(),
        S6.into(),
        true,
    ) {
        Err((_stage, text)) => assert_eq!(text, REFUSED),
        Ok(dump) => panic!("the pipeline accepts S6:\n{dump}"),
    }
    // The oracle's refusal, byte for byte: exit status 1, and one
    // stderr line once the trace pokes are filtered.
    let (accepted, stderr) = oracle_verdict("s6_scope_exit_claim_read_refused.lua", S6);
    assert!(!accepted, "the oracle accepts S6: {stderr:?}");
    assert_eq!(stderr, [REFUSED.to_string()]);
}

#[test]
fn s8_arm_split_do_exit() {
    let (ast, facts) = common::facts_of(S8);
    let dump = alm::dump::render_shape(&facts, &ast);
    let Stmt::Do { body, .. } = &ast[0] else {
        panic!("the program is one do block")
    };
    let Stmt::If { .. } = &body[2] else {
        panic!("the block's third statement is the if")
    };
    let mix_base = site_of(&facts, initializer(&body[0]).id());
    // The If joins `mix` mixed — `{99}` on the then arm, the row
    // `mix_base[0]` on the else arm — so at the block's death
    // `plan_mixed` reads the arms back: the then arm owns a fresh
    // ctor and never defers; the else arm's row has its origin in
    // `mix_base`, still live, so it defers. One deferring arm and one
    // firing arm is the split: the free rides the join's tag, it is
    // `nothing_on` the then arm (the tag's false), and keeps nothing —
    // `mix_base` borrows none of the fresh ctor. The binding is pushed
    // housed and skipped: the block's own free is `mix_base`'s.
    assert_eq!(
        arm_do_exit_at(&dump, 1, 0),
        [ArmSplit {
            at: Some((1, 0)),
            carrier: "mix".into(),
            tag: "if @line 4".into(),
            nothing_on: false,
            keeps: Vec::new(),
        }]
    );
    assert_eq!(facts.arm_do_exit_frees.len(), 1);
    assert_eq!(
        do_exit_at(&dump, 1, 0),
        [Freed {
            site: mix_base,
            carrier: "mix_base".into(),
            keeps: Vec::new(),
        }]
    );
    // The If inside the block owns two arm scopes of its own. Each
    // assigns to `mix`, a binding of the block, so each dies owning
    // nothing: its key lands with an empty list.
    assert_eq!(
        facts.do_exit_frees.len(),
        3,
        "the block and the if's two arms — no other scope died"
    );
    for arm in [0, 1] {
        assert!(
            facts
                .do_exit_frees
                .get(&(body[2].id(), arm))
                .is_some_and(|frees| frees.is_empty()),
            "the if's arm {arm} frees nothing"
        );
    }
    assert!(root_exit(&dump).is_empty());
    assert!(facts.arm_root_exit_frees.is_empty());
    // The tag the split rides is the join's own fact.
    assert_eq!(section(&dump, "join-tags"), ["  @line 4 -> false"]);
    let oracle = oracle_exit_counts("s8_arm_split_do_exit.lua", S8);
    assert_eq!(
        (oracle.arm_split, oracle.do_exit, oracle.root_exit),
        (1, 1, 0)
    );
    let mine = count_exit_families(&facts);
    assert_eq!((mine.arm_split, mine.do_exit, mine.root_exit), (1, 1, 0));
}

#[test]
fn s9_arm_split_root() {
    let (ast, facts) = common::facts_of(S9);
    let dump = alm::dump::render_shape(&facts, &ast);
    let mix_base = site_of(&facts, initializer(&ast[0]).id());
    let Stmt::If { .. } = &ast[2] else {
        panic!("the program's third statement is the if")
    };
    // The same join at the root: the drain finds `mix` mixed and
    // splits it — `nothing_on` the then arm, keeping nothing — and
    // frees `mix_base` plainly.
    assert_eq!(
        arm_root(&dump),
        [ArmSplit {
            at: None,
            carrier: "mix".into(),
            tag: "if @line 3".into(),
            nothing_on: false,
            keeps: Vec::new(),
        }]
    );
    assert_eq!(facts.arm_root_exit_frees.len(), 1);
    assert_eq!(
        root_exit(&dump),
        [Freed {
            site: mix_base,
            carrier: "mix_base".into(),
            keeps: Vec::new(),
        }]
    );
    // The If's two arm scopes died owning nothing (as in S8): their
    // keys land with empty lists and print no line.
    assert_eq!(facts.do_exit_frees.len(), 2, "the if's two arms");
    for arm in [0, 1] {
        assert!(
            facts
                .do_exit_frees
                .get(&(ast[2].id(), arm))
                .is_some_and(|frees| frees.is_empty()),
            "the if's arm {arm} frees nothing"
        );
    }
    assert!(facts.arm_do_exit_frees.is_empty());
    assert_eq!(section(&dump, "join-tags"), ["  @line 3 -> false"]);
    let oracle = oracle_exit_counts("s9_arm_split_root.lua", S9);
    assert_eq!(
        (oracle.arm_split, oracle.do_exit, oracle.root_exit),
        (1, 1, 1)
    );
    let mine = count_exit_families(&facts);
    assert_eq!((mine.arm_split, mine.do_exit, mine.root_exit), (1, 1, 1));
}
