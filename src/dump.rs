//! The per-stage debug dumps — alm-only additive surface with no
//! mirror counterpart, so no future mirror transfer can conflict with
//! it (REBASE_PLAN.md §3.3.2: golden dumps per layer). L2 brings the
//! AST dump (`--dump-ast`); each later stage adds its own renderer
//! here (walk facts at L3, IR at L7, …).
//!
//! Format laws: one node per line, children indented two spaces;
//! statements carry `@line` (the desugar attribution pins become
//! greppable); constructor entries show physical slots and the P8
//! provenance; `NodeId`s are never printed (they churn when a later
//! layer parses modules in-process). Every match is exhaustive with no
//! `_` arm — a new AST variant fails compilation here until the dump
//! grows, so the dump cannot silently drift from the tree it reads.

use crate::ast::{BinOp, CtorKey, Expr, Stmt, UnOp};
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
