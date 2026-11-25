//! The per-stage debug dumps — alm-only additive surface with no
//! mirror counterpart, so no future mirror transfer can conflict with
//! it (REBASE_PLAN.md §3.3.2: golden dumps per layer). L2 brings the
//! AST dump (`--dump-ast`); L3 adds the walk-facts dump
//! (`--dump-shape`); each later stage adds its own renderer here (IR
//! at L7, …).
//!
//! Format laws: one node per line, children indented two spaces;
//! statements carry `@line` (the desugar attribution pins become
//! greppable); constructor entries show physical slots and the P8
//! provenance; `NodeId`s are never printed (they churn when a later
//! layer parses modules in-process) — the shape dump projects every
//! `NodeId`-keyed fact through its node's line instead. Every match is
//! exhaustive with no `_` arm — a new AST variant fails compilation
//! here until the dump grows, so the dump cannot silently drift from
//! the tree it reads.

use crate::ast::{BinOp, CtorKey, Expr, NodeId, Stmt, UnOp};
use crate::shape::{BuiltinVerb, FfiVerb, ShapeFacts};
use std::collections::BTreeMap;
use std::fmt::Write;

/// Renders the post-desugar program exactly as `alm --dump-ast` and
/// the parse goldens print it.
pub fn render_ast(program: &[Stmt]) -> String {
    let mut out = String::new();
    for stmt in program {
        write_stmt(&mut out, stmt, 0);
    }
    out
}

fn write_stmt(out: &mut String, stmt: &Stmt, depth: usize) {
    match stmt {
        Stmt::LocalDecl {
            names, exprs, loc, ..
        } => {
            emit(out, depth, &format!("LocalDecl @{}", loc.line));
            emit(out, depth + 1, &format!("names: {}", names.join(", ")));
            for expr in exprs {
                write_expr(out, expr, depth + 1);
            }
        }
        Stmt::Assignment {
            name, expr, loc, ..
        } => {
            emit(out, depth, &format!("Assignment @{}", loc.line));
            emit(out, depth + 1, &format!("name: {name}"));
            write_expr(out, expr, depth + 1);
        }
        Stmt::IndexAssign {
            obj,
            key,
            value,
            loc,
            ..
        } => {
            emit(out, depth, &format!("IndexAssign @{}", loc.line));
            emit(out, depth + 1, "obj:");
            write_expr(out, obj, depth + 2);
            emit(out, depth + 1, "key:");
            write_expr(out, key, depth + 2);
            emit(out, depth + 1, "value:");
            write_expr(out, value, depth + 2);
        }
        Stmt::While {
            condition,
            body,
            loc,
            ..
        } => {
            emit(out, depth, &format!("While @{}", loc.line));
            emit(out, depth + 1, "cond:");
            write_expr(out, condition, depth + 2);
            for stmt in body {
                write_stmt(out, stmt, depth + 1);
            }
        }
        Stmt::Do { body, loc, .. } => {
            emit(out, depth, &format!("Do @{}", loc.line));
            for stmt in body {
                write_stmt(out, stmt, depth + 1);
            }
        }
        Stmt::If {
            condition,
            then_body,
            else_body,
            loc,
            ..
        } => {
            emit(out, depth, &format!("If @{}", loc.line));
            emit(out, depth + 1, "cond:");
            write_expr(out, condition, depth + 2);
            emit(out, depth + 1, "then:");
            for stmt in then_body {
                write_stmt(out, stmt, depth + 2);
            }
            if !else_body.is_empty() {
                emit(out, depth + 1, "else:");
                for stmt in else_body {
                    write_stmt(out, stmt, depth + 2);
                }
            }
        }
        Stmt::Print { exprs, loc, .. } => {
            emit(out, depth, &format!("Print @{}", loc.line));
            for expr in exprs {
                write_expr(out, expr, depth + 1);
            }
        }
        Stmt::Expr { expr, loc, .. } => {
            emit(out, depth, &format!("ExprStmt @{}", loc.line));
            write_expr(out, expr, depth + 1);
        }
        Stmt::Return { value, loc, .. } => {
            emit(out, depth, &format!("Return @{}", loc.line));
            if let Some(expr) = value {
                write_expr(out, expr, depth + 1);
            }
        }
        Stmt::Break { loc, .. } => {
            emit(out, depth, &format!("Break @{}", loc.line));
        }
    }
}

fn write_expr(out: &mut String, expr: &Expr, depth: usize) {
    match expr {
        Expr::Integer { value, .. } => emit(out, depth, &format!("Integer {value}")),
        Expr::Float { value, .. } => emit(out, depth, &format!("Float {value}")),
        Expr::Boolean { value, .. } => emit(out, depth, &format!("Boolean {value}")),
        Expr::String { value, .. } => emit(out, depth, &format!("String {value:?}")),
        Expr::Nil { .. } => emit(out, depth, "Nil"),
        Expr::TableCtor { entries, line, .. } => {
            emit(out, depth, &format!("TableCtor @{line}"));
            for (key, value) in entries {
                match key {
                    CtorKey::Const {
                        slot,
                        positional: true,
                    } => emit(
                        out,
                        depth + 1,
                        &format!("entry key: slot {slot} (positional)"),
                    ),
                    CtorKey::Const {
                        slot,
                        positional: false,
                    } => emit(
                        out,
                        depth + 1,
                        &format!("entry key: slot {slot} (explicit)"),
                    ),
                    CtorKey::Str(name) => emit(out, depth + 1, &format!("entry key: str {name:?}")),
                    CtorKey::Expr(key) => {
                        emit(out, depth + 1, "entry");
                        emit(out, depth + 2, "key:");
                        write_expr(out, key, depth + 3);
                        emit(out, depth + 2, "value:");
                        write_expr(out, value, depth + 3);
                        continue;
                    }
                }
                write_expr(out, value, depth + 2);
            }
        }
        Expr::Identifier { name, .. } => emit(out, depth, &format!("Identifier {name}")),
        Expr::Index { obj, key, .. } => {
            emit(out, depth, "Index");
            emit(out, depth + 1, "obj:");
            write_expr(out, obj, depth + 2);
            emit(out, depth + 1, "key:");
            write_expr(out, key, depth + 2);
        }
        Expr::BinaryOp {
            op, left, right, ..
        } => {
            emit(out, depth, &format!("BinaryOp {}", op_name(op)));
            write_expr(out, left, depth + 1);
            write_expr(out, right, depth + 1);
        }
        Expr::UnaryOp { op, expr, .. } => {
            emit(out, depth, &format!("UnaryOp {}", unop_name(op)));
            write_expr(out, expr, depth + 1);
        }
        Expr::SysAllocCount { .. } => emit(out, depth, "SysAllocCount"),
        Expr::SysExecCount { .. } => emit(out, depth, "SysExecCount"),
        Expr::FfiModule { .. } => emit(out, depth, "FfiModule"),
        Expr::AsyncModule { .. } => emit(out, depth, "AsyncModule"),
        Expr::Field { obj, name, .. } => {
            emit(out, depth, &format!("Field .{name}"));
            write_expr(out, obj, depth + 1);
        }
        Expr::Function { params, body, .. } => {
            emit(out, depth, "Function");
            emit(out, depth + 1, &format!("params: {}", params.join(", ")));
            for stmt in body {
                write_stmt(out, stmt, depth + 1);
            }
        }
        Expr::Call { callee, args, .. } => {
            emit(out, depth, "Call");
            emit(out, depth + 1, "callee:");
            write_expr(out, callee, depth + 2);
            for arg in args {
                write_expr(out, arg, depth + 1);
            }
        }
    }
}

fn op_name(op: &BinOp) -> &'static str {
    match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::Div => "Div",
        BinOp::IntDiv => "IntDiv",
        BinOp::Mod => "Mod",
        BinOp::LessThan => "LessThan",
        BinOp::GreaterThan => "GreaterThan",
        BinOp::LessEq => "LessEq",
        BinOp::GreaterEq => "GreaterEq",
        BinOp::Equal => "Equal",
        BinOp::NotEqual => "NotEqual",
        BinOp::And => "And",
        BinOp::Or => "Or",
        BinOp::Concat => "Concat",
    }
}

fn unop_name(op: &UnOp) -> &'static str {
    match op {
        UnOp::Neg => "Neg",
        UnOp::Not => "Not",
        UnOp::Len => "Len",
    }
}

fn emit(out: &mut String, depth: usize, text: &str) {
    let _ = writeln!(out, "{}{text}", "  ".repeat(depth));
}

/// Renders the walk's output exactly as `alm --dump-shape` and the L3
/// walk goldens print it. Site indices, ghost ids, and unknown-node ids
/// are the walk's own deterministic mint; `NodeId`-keyed facts project
/// through their node's line (the AST walk below), so two parses of
/// one source dump identically and in-process sweeps stay stable.
pub fn render_shape(facts: &ShapeFacts, ast: &[Stmt]) -> String {
    let mut lines = BTreeMap::new();
    let index = |stmts: &[Stmt], lines: &mut BTreeMap<NodeId, u32>| {
        let mut v = LineCollector {
            lines,
            current_line: 0,
        };
        let _ = crate::visit::walk_stmts(&mut v, stmts);
    };
    index(ast, &mut lines);

    let line_of = |id: NodeId| -> u32 {
        lines
            .get(&id)
            .copied()
            .unwrap_or_else(|| unreachable!("a fact's key node was collected from the AST"))
    };

    let mut out = String::new();
    let mut emitf = |text: String| {
        let _ = writeln!(out, "{text}");
    };

    emitf(format!("sites: {}", facts.sites.len()));
    for idx in 0..facts.elems.len() {
        emitf(format!(
            "  site {idx} @line {} elem {:?} layout {:?}",
            facts.ctor_lines[idx],
            resolve_ty(facts, &facts.elems[idx]),
            facts.layouts[idx],
        ));
    }

    // (the constraint store's substitution map is internal state — the
    // pins' refinement lives there by design; the frozen surface is the
    // resolved types above, which is all a downstream consumer reads.)

    if !facts.cell_children.is_empty() {
        emitf("cell-children:".into());
        for (parent, kids) in &facts.cell_children {
            let list = kids
                .iter()
                .map(|k| k.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            emitf(format!("  site {parent} -> [{list}]"));
        }
    }

    if !facts.row_reads.is_empty() {
        emitf("row-reads:".into());
        for (base, (name, depth)) in &facts.row_reads {
            emitf(format!("  site {base} ({name}, pierce {depth})"));
        }
    }

    if !facts.stored_ctor_parents.is_empty() {
        let list = facts
            .stored_ctor_parents
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(" ");
        emitf(format!("stored-ctor-parents: [{list}]"));
    }

    if !facts.free_sites.is_empty() {
        emitf("frees:".into());
        for stmt in &facts.free_sites {
            let keeps = facts
                .free_keeps
                .get(stmt)
                .map(|k| format!(" keeps: {}", render_keeps(k)))
                .unwrap_or_default();
            emitf(format!("  @line {}{keeps}", line_of(*stmt)));
        }
    }

    // — the exit-fate families (L6): the temp-fate planner's three
    // maps (6.1) — the ctor sites born in a statement, a condition, an
    // and/or operand and freed where the value dies. Site ids print
    // raw like the ghost families; the NodeId keys project through
    // their node's line like every walk family. A section prints only
    // when it has an entry line.
    {
        let mut temp_frees = |header: &str, frees: &BTreeMap<NodeId, Vec<usize>>| {
            let entries: Vec<String> = frees
                .iter()
                .filter(|(_, sites)| !sites.is_empty())
                .map(|(key, sites)| {
                    let list = sites
                        .iter()
                        .map(|s| s.to_string())
                        .collect::<Vec<_>>()
                        .join(" ");
                    format!("  @line {} sites [{list}]", line_of(*key))
                })
                .collect();
            if !entries.is_empty() {
                emitf(format!("{header}:"));
                for entry in entries {
                    emitf(entry);
                }
            }
        };
        temp_frees("stmt-temp-frees", &facts.stmt_temp_frees);
        temp_frees("cond-temp-frees", &facts.cond_temp_frees);
        temp_frees("arm-temp-frees", &facts.arm_temp_frees);
    }

    if !facts.rebind_frees.is_empty() {
        emitf("rebind-grants:".into());
        for (stmt, grants) in &facts.rebind_frees {
            for (name, keeps) in grants {
                emitf(format!(
                    "  @line {} {name} keeps: {}",
                    line_of(*stmt),
                    render_keeps(keeps)
                ));
            }
        }
    }

    if !facts.arm_free_sites.is_empty() {
        emitf("arm-frees:".into());
        for (stmt, entries) in &facts.arm_free_sites {
            for e in entries {
                emitf(format!(
                    "  @line {} {} tag {} nothing_on={} keeps: {}",
                    line_of(*stmt),
                    e.carrier,
                    render_tag(&e.tag, &line_of),
                    e.nothing_on,
                    render_keeps(&e.keeps)
                ));
            }
        }
    }

    if !facts.arm_rebind_frees.is_empty() {
        emitf("arm-rebind-frees:".into());
        for (stmt, entries) in &facts.arm_rebind_frees {
            for e in entries {
                emitf(format!(
                    "  @line {} {} tag {} nothing_on={} keeps: {}",
                    line_of(*stmt),
                    e.carrier,
                    render_tag(&e.tag, &line_of),
                    e.nothing_on,
                    render_keeps(&e.keeps)
                ));
            }
        }
    }

    if !facts.join_tags.is_empty() {
        emitf("join-tags:".into());
        for (stmt, defer) in &facts.join_tags {
            emitf(format!("  @line {} -> {defer}", line_of(*stmt)));
        }
    }

    if !facts.call_tags.is_empty() {
        emitf("call-tags:".into());
        for (expr, defers) in &facts.call_tags {
            let list = defers
                .iter()
                .map(|d| d.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            emitf(format!("  @line {} -> [{list}]", line_of(*expr)));
        }
    }

    if !facts.move_poisons.is_empty() {
        emitf("move-poisons:".into());
        for (stmt, names) in &facts.move_poisons {
            let list = names.iter().cloned().collect::<Vec<_>>().join(" ");
            emitf(format!("  @line {}: {list}", line_of(*stmt)));
        }
    }

    if !facts.store_ghost_keeps.is_empty() {
        emitf("store-ghost-keeps:".into());
        for (stmt, ghosts) in &facts.store_ghost_keeps {
            let list = ghosts
                .iter()
                .map(|g| g.to_string())
                .collect::<Vec<_>>()
                .join(" ");
            emitf(format!("  @line {} ghosts [{list}]", line_of(*stmt)));
        }
    }

    if !facts.ctor_ghost_keeps.is_empty() {
        emitf("ctor-ghost-keeps:".into());
        for (expr, keeps) in &facts.ctor_ghost_keeps {
            for (entry, ghost) in keeps {
                emitf(format!(
                    "  @line {} entry {entry} ghost {ghost}",
                    line_of(*expr)
                ));
            }
        }
    }

    if !facts.fn_scope_keys.is_empty() {
        emitf("fn-scope-keys:".into());
        for (fn_ptr, (owner, arm)) in &facts.fn_scope_keys {
            emitf(format!(
                "  fn @line {} -> (@line {}, arm {arm})",
                line_of(*fn_ptr),
                line_of(*owner)
            ));
        }
    }

    if !facts.fn_touched.is_empty() {
        emitf("fn-touched:".into());
        for (fn_ptr, names) in &facts.fn_touched {
            let list = names.iter().cloned().collect::<Vec<_>>().join(" ");
            emitf(format!("  fn @line {}: {list}", line_of(*fn_ptr)));
        }
    }

    if !facts.fn_capture_depths.is_empty() {
        emitf("fn-capture-depths:".into());
        for (fn_ptr, captures) in &facts.fn_capture_depths {
            for (name, depth) in captures {
                emitf(format!("  fn @line {} {name} @d{depth}", line_of(*fn_ptr)));
            }
        }
    }

    if !facts.fn_body_depths.is_empty() {
        emitf("fn-body-depths:".into());
        for (fn_ptr, depth) in &facts.fn_body_depths {
            emitf(format!("  fn @line {} @d{depth}", line_of(*fn_ptr)));
        }
    }

    // — the fast-lane families (L5): the reserve plans a conversion
    // loop minted and the store eligibility facts the post-walk scan
    // proved. NodeId keys project through their node's line like every
    // walk family; the plan's ctor reserves print as the stores' lines
    // in mint order (the NodeId space is parse order).
    if !facts.fast_stores.is_empty() {
        emitf("fast-stores:".into());
        for (stmt, elig) in &facts.fast_stores {
            emitf(format!(
                "  store @line {} {} key {:?} row_reserve {} loop @line {}",
                line_of(*stmt),
                elig.table,
                elig.key,
                elig.row_reserve,
                line_of(elig.loop_id),
            ));
        }
    }

    if !facts.reserve_plans.is_empty() {
        emitf("reserve-plans:".into());
        for (loop_id, plan) in &facts.reserve_plans {
            let names = |v: &[String]| {
                if v.is_empty() {
                    "—".to_string()
                } else {
                    v.join(" ")
                }
            };
            let ctors = plan
                .ctor_reserves
                .iter()
                .map(|s| format!("@line {}", line_of(*s)))
                .collect::<Vec<_>>()
                .join(" ");
            let ctors = if ctors.is_empty() {
                "—".to_string()
            } else {
                ctors
            };
            let opt = |k: &Option<i64>| k.map(|v| v.to_string()).unwrap_or_else(|| "—".to_string());
            emitf(format!(
                "  loop @line {} pre [{}] pre-sat [{}] nested [{}] ctor-reserves [{}] entry-lb {} key-offset {}",
                line_of(*loop_id),
                names(&plan.pre_header),
                names(&plan.pre_satisfied),
                names(&plan.nested),
                ctors,
                opt(&plan.entry_lb),
                opt(&plan.key_offset),
            ));
        }
    }

    // — the checker-minted families (L4). Instance ids are the
    // checker's own per-compile counter; every NodeId-keyed entry
    // projects through its node's line like the walk's.
    if let Some(elem) = &facts.boundary_elem {
        emitf("boundary-elem:".into());
        emitf(format!(
            "  elem {}",
            render_ty(&resolve_ty(facts, elem), &line_of)
        ));
    }

    if !facts.fn_defs.is_empty() {
        emitf("fn-defs:".into());
        for (ptr, def) in &facts.fn_defs {
            let sig = def
                .signature
                .as_ref()
                .map(|sig| {
                    sig.iter()
                        .map(|ty| render_ty(&resolve_ty(facts, ty), &line_of))
                        .collect::<Vec<_>>()
                        .join(",")
                })
                .unwrap_or_else(|| "—".to_string());
            emitf(format!(
                "  fn @line {} params {} ret {} sig {sig}",
                line_of(*ptr),
                def.params.len(),
                render_ty(&resolve_ty(facts, &def.ret), &line_of),
            ));
        }
    }

    if !facts.env_faces.is_empty() {
        emitf("env-faces:".into());
        for (ptr, face) in &facts.env_faces {
            for (name, ty) in face {
                emitf(format!(
                    "  fn @line {} {name} {}",
                    line_of(*ptr),
                    render_ty(&resolve_ty(facts, ty), &line_of),
                ));
            }
        }
    }

    if !facts.env_face_depths.is_empty() {
        emitf("env-face-depths:".into());
        for (ptr, depths) in &facts.env_face_depths {
            for (name, depth) in depths {
                emitf(format!("  fn @line {} {name} @d{depth}", line_of(*ptr)));
            }
        }
    }

    if !facts.closure_fields.is_empty() {
        emitf("closure-fields:".into());
        for ((site, field), ptr) in &facts.closure_fields {
            emitf(format!(
                "  ctor site {site} @line {} field {field} -> fn @line {}",
                facts.ctor_lines[*site],
                line_of(*ptr),
            ));
        }
    }

    if !facts.call_fns.is_empty() {
        emitf("call-fns:".into());
        for (call, fns) in &facts.call_fns {
            let list = fns
                .iter()
                .map(|f| format!("@line {}", line_of(*f)))
                .collect::<Vec<_>>()
                .join(" ");
            emitf(format!("  call @line {} -> fn {list}", line_of(*call)));
        }
    }

    if !facts.instances.is_empty() {
        emitf("instances:".into());
        for (id, rec) in &facts.instances {
            let head = match (rec.call, rec.fn_node) {
                (Some(call), Some(f)) => format!(
                    "  instance #{} call @line {} fn @line {}",
                    id.0,
                    line_of(call),
                    line_of(f),
                ),
                _ => format!("  instance #{} (root extent)", id.0),
            };
            let tail = rec
                .ret
                .as_ref()
                .map(|ty| format!(" ret {}", render_ty(&resolve_ty(facts, ty), &line_of)))
                .unwrap_or_default();
            emitf(format!("{head}{tail}"));
            for (call, kids) in &rec.children {
                let list = kids
                    .iter()
                    .map(|k| format!("#{}", k.0))
                    .collect::<Vec<_>>()
                    .join(" ");
                emitf(format!("    child call @line {} -> {list}", line_of(*call)));
            }
            for (node, ptr) in &rec.creation_envs {
                emitf(format!(
                    "    creation @line {} -> fn @line {}",
                    line_of(*node),
                    line_of(*ptr),
                ));
            }
            for node in &rec.closure_calls {
                emitf(format!("    closure-call @line {}", line_of(*node)));
            }
            for (node, lane) in &rec.index_key_lanes {
                emitf(format!("    key @line {} {:?}", line_of(*node), lane,));
            }
            for (node, ty) in &rec.access_elems {
                emitf(format!(
                    "    access @line {} {}",
                    line_of(*node),
                    render_ty(&resolve_ty(facts, ty), &line_of),
                ));
            }
        }
    }

    if !facts.ffi_verbs.is_empty() {
        emitf("ffi-verbs:".into());
        for (node, verb) in &facts.ffi_verbs {
            let verb = match verb {
                FfiVerb::Load => "load".to_string(),
                FfiVerb::ArgKind => "arg-kind".to_string(),
                FfiVerb::Cdef => "cdef".to_string(),
                FfiVerb::New { name } => format!("new '{name}'"),
                FfiVerb::Sizeof { bytes } => format!("sizeof {bytes}"),
                FfiVerb::AsyncCreate => "async-create".to_string(),
                FfiVerb::AsyncResume => "async-resume".to_string(),
                FfiVerb::AsyncYield => "async-yield".to_string(),
                FfiVerb::AsyncStatus => "async-status".to_string(),
                FfiVerb::AsyncClose => "async-close".to_string(),
                FfiVerb::Drive { base, sym } => format!("drive {base}.{sym}"),
            };
            emitf(format!("  @line {} {verb}", line_of(*node)));
        }
    }

    if !facts.builtin_verbs.is_empty() {
        emitf("builtin-verbs:".into());
        for (node, verb) in &facts.builtin_verbs {
            let verb = match verb {
                BuiltinVerb::Assert => "assert",
                BuiltinVerb::Error => "error",
                BuiltinVerb::ToNumber => "tonumber",
            };
            emitf(format!("  @line {} {verb}", line_of(*node)));
        }
    }

    if !facts.ffi_mints.is_empty() {
        emitf("ffi-mints:".into());
        for (node, mint) in &facts.ffi_mints {
            emitf(format!(
                "  @line {} name '{}' elem {} capacity {}",
                line_of(*node),
                mint.name,
                render_ty(&resolve_ty(facts, &mint.elem), &line_of),
                mint.capacity,
            ));
        }
    }

    if !facts.local_types.is_empty() {
        emitf("local-types:".into());
        for ((stmt, inst, name), ty) in &facts.local_types {
            emitf(format!(
                "  stmt @line {} #{} {name} {}",
                line_of(*stmt),
                inst.0,
                render_ty(&resolve_ty(facts, ty), &line_of),
            ));
        }
    }

    if !facts.adopt_lines.is_empty() {
        emitf("adopt-lines:".into());
        for (name, line) in &facts.adopt_lines {
            emitf(format!("  {name} @line {line}"));
        }
    }

    if !facts.diagnostics.is_empty() {
        emitf("diagnostics:".into());
        for d in &facts.diagnostics {
            emitf(format!("  {}", d.render()));
        }
    }

    out
}

struct LineCollector<'a> {
    lines: &'a mut BTreeMap<NodeId, u32>,
    current_line: u32,
}

impl crate::visit::Visitor for LineCollector<'_> {
    type Break = std::convert::Infallible;

    fn enter_stmt(&mut self, stmt: &Stmt) -> Result<(), Self::Break> {
        self.current_line = stmt.loc().line;
        self.lines.insert(stmt.id(), stmt.loc().line);
        Ok(())
    }

    fn enter_expr(&mut self, expr: &Expr) -> Result<(), Self::Break> {
        // A ctor carries its own line (the site's); every other
        // expression borrows its enclosing statement's — the only
        // location the tree offers them.
        let line = match expr {
            Expr::TableCtor { line, .. } => *line,
            _ => self.current_line,
        };
        self.lines.insert(expr.id(), line);
        Ok(())
    }
}

fn resolve_ty(facts: &ShapeFacts, ty: &crate::shape::Ty) -> crate::shape::Ty {
    facts.resolved(ty)
}

/// The dump's `Ty` text: `Debug`'s shape, except a `Closure`'s
/// `NodeId` projects through its node's line — the dump law (raw
/// NodeIds churn across in-process parses; lines do not).
fn render_ty(ty: &crate::shape::Ty, line_of: &impl Fn(NodeId) -> u32) -> String {
    match ty {
        crate::shape::Ty::Pending => "Pending".to_string(),
        crate::shape::Ty::Int => "Int".to_string(),
        crate::shape::Ty::Flt => "Flt".to_string(),
        crate::shape::Ty::Bool => "Bool".to_string(),
        crate::shape::Ty::Str => "Str".to_string(),
        crate::shape::Ty::Tbl(inner) => format!("Tbl({})", render_ty(inner, line_of)),
        crate::shape::Ty::Ffi => "Ffi".to_string(),
        crate::shape::Ty::FfiLib => "FfiLib".to_string(),
        crate::shape::Ty::Async => "Async".to_string(),
        crate::shape::Ty::Any => "Any".to_string(),
        crate::shape::Ty::Closure(ptr) => format!("Closure(@line {})", line_of(*ptr)),
        crate::shape::Ty::Unknown(id) => format!("Unknown({id})"),
        crate::shape::Ty::Conflict => "Conflict".to_string(),
    }
}

fn render_keeps(keeps: &[crate::shape::Keep]) -> String {
    keeps
        .iter()
        .map(|k| match k {
            crate::shape::Keep::Name(n) => n.clone(),
            crate::shape::Keep::Ghost(g) => format!("ghost {g}"),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_tag(tag: &crate::shape::TagSrc, line_of: &impl Fn(NodeId) -> u32) -> String {
    match tag {
        crate::shape::TagSrc::If(stmt) => format!("if @line {}", line_of(*stmt)),
        crate::shape::TagSrc::Call(expr) => format!("call @line {}", line_of(*expr)),
    }
}

#[cfg(test)]
mod tests {
    use super::render_ast;
    use crate::pipeline::front;
    use crate::source::SourceFile;
    use crate::surface::{Flag, Surface};

    fn dump(source: &str, flags: &[&str]) -> String {
        let mut surface = Surface::default();
        for flag in flags {
            Flag::parse(flag)
                .expect("test uses legal flags only")
                .apply(&mut surface);
        }
        let src = SourceFile::new("dump.lua", source);
        let out = front(&src, &surface);
        assert!(out.is_ok(), "{:?}", out.diagnostics);
        render_ast(&out.ast)
    }

    #[test]
    fn the_shape_golden_ctor_and_for_latch() {
        // The reference shape for the two headline laws: the ctor-key
        // provenance (positional vs explicit, physical slots — an array
        // ctor may hold both; a record key would make it mixed, which
        // the parser refuses) and the exclusive for-latch.
        // `--index-base=1` shifts only the explicit key (twin below).
        assert_eq!(
            dump(
                "local t = {[10] = 1, \"x\"}\nlocal r = {name = 2}\nfor i = 1, 3 do\n    print(i)\nend\n",
                &[]
            ),
            "LocalDecl @1\n\
             \x20 names: t\n\
             \x20 TableCtor @1\n\
             \x20   entry key: slot 10 (explicit)\n\
             \x20     Integer 1\n\
             \x20   entry key: slot 0 (positional)\n\
             \x20     String \"x\"\n\
             LocalDecl @2\n\
             \x20 names: r\n\
             \x20 TableCtor @2\n\
             \x20   entry key: str \"name\"\n\
             \x20     Integer 2\n\
             Do @3\n\
             \x20 LocalDecl @3\n\
             \x20   names: i\n\
             \x20   Integer 1\n\
             \x20 LocalDecl @3\n\
             \x20   names: for$limit\n\
             \x20   Integer 3\n\
             \x20 While @3\n\
             \x20   cond:\n\
             \x20     BinaryOp LessThan\n\
             \x20       Identifier i\n\
             \x20       Identifier for$limit\n\
             \x20   Do @3\n\
             \x20     Print @4\n\
             \x20       Identifier i\n\
             \x20   Assignment @3\n\
             \x20     name: i\n\
             \x20     BinaryOp Add\n\
             \x20       Identifier i\n\
             \x20       Integer 1\n"
        );
    }

    #[test]
    fn index_base_shifts_only_the_explicit_key() {
        assert_eq!(
            dump("local t = {[10] = 1, \"x\"}\n", &["--index-base=1"]),
            "LocalDecl @1\n\
             \x20 names: t\n\
             \x20 TableCtor @1\n\
             \x20   entry key: slot 9 (explicit)\n\
             \x20     Integer 1\n\
             \x20   entry key: slot 0 (positional)\n\
             \x20     String \"x\"\n"
        );
    }

    #[test]
    fn inclusive_latch_folds_limit_plus_one_at_the_latch() {
        assert_eq!(
            dump(
                "for i = 1, 3 do\n    print(i)\nend\n",
                &["--for-limit=inclusive"]
            ),
            "Do @1\n\
             \x20 LocalDecl @1\n\
             \x20   names: i\n\
             \x20   Integer 1\n\
             \x20 LocalDecl @1\n\
             \x20   names: for$limit\n\
             \x20   BinaryOp Add\n\
             \x20     Integer 3\n\
             \x20     Integer 1\n\
             \x20 While @1\n\
             \x20   cond:\n\
             \x20     BinaryOp LessThan\n\
             \x20       Identifier i\n\
             \x20       Identifier for$limit\n\
             \x20   Do @1\n\
             \x20     Print @2\n\
             \x20       Identifier i\n\
             \x20   Assignment @1\n\
             \x20     name: i\n\
             \x20     BinaryOp Add\n\
             \x20       Identifier i\n\
             \x20       Integer 1\n"
        );
    }

    #[test]
    fn expr_key_entries_and_bare_returns() {
        assert_eq!(
            dump("local k = 1\nlocal t = {[k] = 2}\nreturn\n", &[]),
            "LocalDecl @1\n\
             \x20 names: k\n\
             \x20 Integer 1\n\
             LocalDecl @2\n\
             \x20 names: t\n\
             \x20 TableCtor @2\n\
             \x20   entry\n\
             \x20     key:\n\
             \x20       Identifier k\n\
             \x20     value:\n\
             \x20       Integer 2\n\
             Return @3\n"
        );
    }
}
