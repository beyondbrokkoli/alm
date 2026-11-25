//! The exit-fate pins (L6_DESIGN.md §6): the temp-fate programs of
//! `L6_PORT_MAP.md` §7, each asserting what the organ's law says —
//! derived from its code, never from a run — and carrying the oracle's
//! own count for its source (L6_HARNESS.md §3). Facts are addressed
//! through the rendered dump: a section by name, a statement by line,
//! a ctor site by the line it was born on — never a raw id. Where two
//! ctors share a line (T9, L1 and its control) the pin destructures
//! the statement to the ctor nodes instead.
//!
//! The one lease, `known_lease/field-obj-arm-scan`, asserts the
//! correct behaviour under `common::xfail`: it must fail until the
//! chartered fix, and a pass fails the run.

mod common;

use alm::ast::{BinOp, Expr, NodeId, Stmt};
use alm::shape::ShapeFacts;
use common::{oracle_exit_counts, section, site_of, xfail};

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
