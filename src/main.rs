use logos::Logos;
use std::ffi::{CString, c_void};
use std::process::Stdio;

mod analysis;
mod ast;
mod backend;
mod debug;
mod ir;
mod lexer;
mod lowerer;
mod parser;
#[cfg(test)]
mod property_tests;
mod shape;

use ast::Stmt;

// The boundary type, shared by construction: the same #[repr(C)] struct
use alm_rt::rt::AlmTable;

type AlmExec = unsafe extern "C" fn(args: *mut AlmTable) -> *mut AlmTable;
type AlmTblNew = unsafe extern "C" fn(esize: usize, flags: u8) -> *mut AlmTable;
type AlmTblSet = unsafe extern "C" fn(t: *mut AlmTable, index: i64, val: *const u8);
type AlmTblSetAny = unsafe extern "C" fn(t: *mut AlmTable, index: i64, val: i128);
type AlmTblGet = unsafe extern "C" fn(t: *mut AlmTable, index: i64, dst: *mut u8, esize: usize);
type AlmTblFree = unsafe extern "C" fn(t: *mut AlmTable);
type AlmStrIntern = unsafe extern "C" fn(s: *const u8, len: usize) -> *const u8;
type AlmArgKind = unsafe extern "C" fn() -> i32;

fn poke_build_fail() {
    alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_BUILD_FAIL);
    eprintln!("ALM_TRACE: slot 1 — build failed");
}

fn fail_build(diags: &[String]) -> ! {
    for d in diags {
        eprintln!("{d}");
    }
    poke_build_fail();
    std::process::exit(1)
}

enum HostArg {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str(Vec<u8>),
    Any(i128),
}

fn parse_word(raw: &str, kind: i32) -> Result<HostArg, ()> {
    match kind {
        alm_rt::rt::ALM_ARG_INT => raw.parse::<i64>().map(HostArg::Int).map_err(|_| ()),
        alm_rt::rt::ALM_ARG_FLOAT => raw.parse::<f64>().map(HostArg::Float).map_err(|_| ()),
        alm_rt::rt::ALM_ARG_BOOL => match raw {
            "true" => Ok(HostArg::Bool(true)),
            "false" => Ok(HostArg::Bool(false)),
            _ => Err(()),
        },
        alm_rt::rt::ALM_ARG_STRING => Ok(HostArg::Str(raw.as_bytes().to_vec())),
        alm_rt::rt::ALM_ARG_ANY => {
            use alm_rt::rt::ALM_ARG_FLOAT as K_FLOAT;
            use alm_rt::rt::ALM_ARG_INT as K_INT;
            let cell = match alm_rt::classify_word(raw.as_bytes()) {
                alm_rt::AnyWord::Int(v) => alm_rt::alm_any_pack(K_INT, v as u64),
                alm_rt::AnyWord::Float(v) => alm_rt::alm_any_pack(K_FLOAT, v.to_bits()),
                alm_rt::AnyWord::Bool(v) => {
                    alm_rt::alm_any_pack(alm_rt::rt::ALM_ARG_BOOL, u64::from(v))
                }
                alm_rt::AnyWord::Str => {
                    return Ok(HostArg::Str(raw.as_bytes().to_vec()));
                }
            };
            Ok(HostArg::Any(cell))
        }
        _ => Err(()),
    }
}

const RTLD_NOW: i32 = 0x2;
const RTLD_LOCAL: i32 = 0x1;

unsafe extern "C" {
    fn dlopen(filename: *const i8, flags: i32) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const i8) -> *mut c_void;
}

unsafe fn resolve_symbol<T>(dylib: *mut c_void, name: &[u8]) -> Result<T, String> {
    let sym = unsafe { dlsym(dylib, name.as_ptr().cast()) };
    if sym.is_null() {
        let sym_name = String::from_utf8_lossy(&name[..name.len() - 1]);
        return Err(format!("dlsym: '{sym_name}' not found"));
    }
    Ok(unsafe { std::mem::transmute_copy::<*mut c_void, T>(&sym) })
}

fn references_arg(stmts: &[Stmt]) -> bool {
    fn expr(e: &ast::Expr) -> bool {
        match e {
            ast::Expr::Identifier(name) => name == "arg",
            ast::Expr::TableCtor { entries, .. } => entries
                .iter()
                .any(|(k, v)| matches!(k, ast::CtorKey::Expr(ke) if expr(ke)) || expr(v)),
            ast::Expr::Index { obj, key } => expr(obj) || expr(key),
            ast::Expr::BinaryOp { left, right, .. } => expr(left) || expr(right),
            ast::Expr::UnaryOp { expr: inner, .. } => expr(inner),
            ast::Expr::Call { callee, args } => expr(callee) || args.iter().any(expr),
            ast::Expr::Function { body, .. } => go(body),
            ast::Expr::Integer(_)
            | ast::Expr::Float(_)
            | ast::Expr::Boolean(_)
            | ast::Expr::String(_)
            | ast::Expr::Nil
            | ast::Expr::SysAllocCount
            | ast::Expr::SysExecCount
            | ast::Expr::FfiModule
            | ast::Expr::CoroModule => false,
            ast::Expr::Field { obj, .. } => expr(obj),
        }
    }
    fn go(stmts: &[Stmt]) -> bool {
        stmts.iter().any(|s| match s {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => exprs.iter().any(expr),
            Stmt::Assignment { expr: value, .. } => expr(value),
            Stmt::IndexAssign {
                obj, key, value, ..
            } => expr(obj) || expr(key) || expr(value),
            Stmt::While {
                condition, body, ..
            } => expr(condition) || go(body),
            Stmt::Do { body, .. } => go(body),
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => expr(condition) || go(then_body) || go(else_body),
            Stmt::Expr { expr: inner, .. } => expr(inner),
            Stmt::Return { value, .. } => value.as_ref().is_some_and(expr),
            Stmt::Break { .. } => false,
        })
    }
    go(stmts)
}

fn uses_ffi(stmts: &[Stmt]) -> bool {
    fn expr(e: &ast::Expr) -> bool {
        match e {
            ast::Expr::FfiModule => true,
            ast::Expr::Field { obj, .. } => expr(obj),
            ast::Expr::TableCtor { entries, .. } => entries
                .iter()
                .any(|(k, v)| matches!(k, ast::CtorKey::Expr(ke) if expr(ke)) || expr(v)),
            ast::Expr::Index { obj, key } => expr(obj) || expr(key),
            ast::Expr::BinaryOp { left, right, .. } => expr(left) || expr(right),
            ast::Expr::UnaryOp { expr: inner, .. } => expr(inner),
            ast::Expr::Call { callee, args } => expr(callee) || args.iter().any(expr),
            ast::Expr::Function { body, .. } => go(body),
            ast::Expr::Integer(_)
            | ast::Expr::Float(_)
            | ast::Expr::Boolean(_)
            | ast::Expr::String(_)
            | ast::Expr::Nil
            | ast::Expr::SysAllocCount
            | ast::Expr::SysExecCount
            | ast::Expr::CoroModule
            | ast::Expr::Identifier(_) => false,
        }
    }
    fn go(stmts: &[Stmt]) -> bool {
        stmts.iter().any(|s| match s {
            Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => exprs.iter().any(expr),
            Stmt::Assignment { expr: value, .. } => expr(value),
            Stmt::IndexAssign {
                obj, key, value, ..
            } => expr(obj) || expr(key) || expr(value),
            Stmt::While {
                condition, body, ..
            } => expr(condition) || go(body),
            Stmt::Do { body, .. } => go(body),
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => expr(condition) || go(then_body) || go(else_body),
            Stmt::Expr { expr: inner, .. } => expr(inner),
            Stmt::Return { value, .. } => value.as_ref().is_some_and(expr),
            Stmt::Break { .. } => false,
        })
    }
    go(stmts)
}

unsafe fn run_boundary(words: &[String], out_path: &str) -> Result<(), String> {
    let dl_path = if out_path.contains('/') {
        out_path.to_string()
    } else {
        format!("./{out_path}")
    };

    let path = CString::new(dl_path).unwrap();
    let dylib = unsafe { dlopen(path.as_ptr(), RTLD_NOW | RTLD_LOCAL) };
    if dylib.is_null() {
        return Err(format!("dlopen: could not load {out_path}"));
    }

    let alm_exec: AlmExec = unsafe { resolve_symbol(dylib, b"alm_exec\0")? };
    let alm_tbl_new: AlmTblNew = unsafe { resolve_symbol(dylib, b"alm_tbl_new\0")? };
    let alm_tbl_set: AlmTblSet = unsafe { resolve_symbol(dylib, b"alm_tbl_set\0")? };
    let alm_tbl_set_any: AlmTblSetAny = unsafe { resolve_symbol(dylib, b"alm_tbl_set_any\0")? };
    let alm_tbl_get: AlmTblGet = unsafe { resolve_symbol(dylib, b"alm_tbl_get\0")? };
    let alm_tbl_free: AlmTblFree = unsafe { resolve_symbol(dylib, b"alm_tbl_free\0")? };
    let alm_str_intern: AlmStrIntern = unsafe { resolve_symbol(dylib, b"alm_str_intern\0")? };
    let alm_arg_kind: AlmArgKind = unsafe { resolve_symbol(dylib, b"alm_arg_kind\0")? };

    let kind = unsafe { alm_arg_kind() };
    let mut args = std::ptr::null_mut::<AlmTable>();
    if kind != alm_rt::rt::ALM_ARG_NONE {
        let esize = match kind {
            alm_rt::rt::ALM_ARG_BOOL => 1,
            alm_rt::rt::ALM_ARG_ANY => 16,
            _ => 8,
        };
        args = unsafe { alm_tbl_new(esize, ((kind as u8) & 0x07) << 1) };
        let mut parsed = Vec::with_capacity(words.len());
        for raw in words {
            match parse_word(raw, kind) {
                Ok(v) => parsed.push(v),
                Err(()) => {
                    eprintln!(
                        "alm host error: boundary args must be {}, got '{raw}' — \
                         the arg table is {}",
                        arg_kind_words(kind),
                        arg_kind_table(kind),
                    );
                    unsafe { alm_tbl_free(args) };
                    std::process::exit(1);
                }
            }
        }
        for (i, v) in parsed.iter().enumerate() {
            match v {
                HostArg::Int(x) => unsafe {
                    alm_tbl_set(args, i as i64, (x as *const i64).cast::<u8>())
                },
                HostArg::Float(x) => unsafe {
                    alm_tbl_set(args, i as i64, (x as *const f64).cast::<u8>())
                },
                HostArg::Bool(b) => unsafe {
                    alm_tbl_set(args, i as i64, (&u8::from(*b) as *const u8).cast::<u8>())
                },
                HostArg::Str(bytes) => unsafe {
                    let p = alm_str_intern(bytes.as_ptr(), bytes.len());
                    if kind == alm_rt::rt::ALM_ARG_ANY {
                        let cell = alm_rt::alm_any_pack(alm_rt::rt::ALM_ARG_STRING, p as u64);
                        alm_tbl_set_any(args, i as i64, cell);
                    } else {
                        alm_tbl_set(args, i as i64, (&p as *const *const u8).cast::<u8>());
                    }
                },
                HostArg::Any(v) => unsafe { alm_tbl_set_any(args, i as i64, *v) },
            }
        }
    }

    let result = unsafe { alm_exec(args) };

    if result.is_null() {
        eprintln!("[alm host] boundary: alm_exec returned null");
    } else {
        let report = unsafe { render_boundary(result, 0, alm_tbl_get) };
        eprintln!("[alm host] boundary: alm_exec returned {report}");
    }

    unsafe {
        if result != args {
            alm_tbl_free(args);
        }
        alm_tbl_free(result);
    }
    Ok(())
}

unsafe fn render_boundary(t: *mut AlmTable, depth: u32, alm_tbl_get: AlmTblGet) -> String {
    let body = unsafe { render_cells(t, depth, alm_tbl_get) };
    if depth == 0 {
        format!("a table {body}")
    } else {
        format!("row{body}")
    }
}

unsafe fn render_cells(t: *mut AlmTable, depth: u32, alm_tbl_get: AlmTblGet) -> String {
    let (len, esize, contains_tables) = unsafe { ((*t).len, (*t).esize, (*t).contains_tables) };
    let rows = contains_tables != 0 && esize == 8;
    let shown = len.clamp(0, if depth == 0 { 8 } else { 4 }) as usize;
    let mut cells = Vec::with_capacity(shown);
    for i in 0..shown as i64 {
        let mut buf = [0u8; 16];
        unsafe { alm_tbl_get(t, i, buf.as_mut_ptr(), esize) };
        if rows {
            let row = usize::from_ne_bytes(buf[..8].try_into().unwrap()) as *mut AlmTable;
            cells.push(if row.is_null() {
                "null".to_string()
            } else if !is_plausible_row(row as usize) {
                format!("row@{:#x}?", row as usize)
            } else if depth < 2 {
                unsafe { render_boundary(row, depth + 1, alm_tbl_get) }
            } else {
                "row…".to_string()
            });
        } else if esize == 16 {
            let payload = u64::from_ne_bytes(buf[..8].try_into().unwrap());
            let tag = i32::from_ne_bytes(buf[8..12].try_into().unwrap());
            cells.push(match tag {
                k if k == alm_rt::rt::ALM_ARG_INT => format!("{}:int", payload as i64),
                k if k == alm_rt::rt::ALM_ARG_FLOAT => {
                    format!("{}:float", f64::from_bits(payload))
                }
                k if k == alm_rt::rt::ALM_ARG_BOOL => format!("{}:bool", payload != 0),
                k if k == alm_rt::rt::ALM_ARG_STRING => format!("{payload:#x}:string"),
                _ => format!("{payload}:int"),
            });
        } else if esize == 8 {
            cells.push(i64::from_ne_bytes(buf[..8].try_into().unwrap()).to_string());
        } else {
            cells.push((buf[0] != 0).to_string());
        }
    }
    let flag = if rows { ", contains-rows" } else { "" };
    format!("(len={len}, esize={esize}{flag}): [{}]", cells.join(", "))
}

fn is_plausible_row(addr: usize) -> bool {
    #[cfg(target_pointer_width = "64")]
    let is_user_space = addr < 0x0000_7FFF_FFFF_FFFF;
    #[cfg(not(target_pointer_width = "64"))]
    let is_user_space = true;
    addr > 0x0100_0000 && is_user_space && (addr & 7) == 0
}

fn main() {
    alm_rt::trace::compiler_trace_init();

    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        poke_build_fail();
        default_hook(info);
    }));

    let args: Vec<String> = std::env::args().collect();
    const HELP: &str = "\
Usage: alm [FLAGS] [--output <path>] <file.lua> [args...]

FLAGS:
    --help        Print this help message and exit.
    --verbose     Pass clang stdout/stderr through to the console.
    --exe         Link a standalone executable (@main entry, no boundary table).
    --lib         Link a shared library (default; explicit for clarity).
    --debug       -O0, frame pointers, no inlining — dev loop tracing.

The compiler performs a pure transform to native code. If --output is omitted,
it defaults to libalm_out.so (or alm_out for --exe).";

    let mut standalone = false;
    let mut debug = false;
    let mut verbose = false;
    let mut output_file: Option<String> = None;
    let mut idx = 1;
    while let Some(flag) = args.get(idx).map(String::as_str) {
        match flag {
            "--help" => {
                println!("{HELP}");
                std::process::exit(0);
            }
            "--exe" => {
                standalone = true;
                idx += 1;
            }
            "--lib" => {
                standalone = false;
                idx += 1;
            }
            "--debug" => {
                debug = true;
                idx += 1;
            }
            "--verbose" => {
                verbose = true;
                idx += 1;
            }
            "-o" | "--output" => {
                idx += 1;
                if let Some(p) = args.get(idx) {
                    if std::path::Path::new(p.as_str()).is_dir() {
                        eprintln!(
                            "alm compiler error: --output must be a file path, not a directory: {p}"
                        );
                        std::process::exit(1);
                    }
                    output_file = Some(p.clone());
                } else {
                    eprintln!("alm compiler error: --output requires a file path argument");
                    std::process::exit(1);
                }
                idx += 1;
            }
            _ if flag.starts_with("--output=") => {
                output_file = Some(flag["--output=".len()..].to_string());
                idx += 1;
            }
            _ if flag.starts_with('-') => {
                eprintln!(
                    "alm compiler error: Unknown flag '{flag}'. Flags must come before the source file."
                );
                std::process::exit(1);
            }
            _ => break,
        }
    }

    let output_file = output_file.unwrap_or_else(|| {
        if standalone {
            "alm_out".to_string()
        } else {
            "libalm_out.so".to_string()
        }
    });

    if args.len() <= idx {
        eprintln!("{HELP}");
        std::process::exit(1);
    }
    let source_path = &args[idx];
    let source = std::fs::read_to_string(source_path).unwrap_or_else(|e| {
        let cwd = std::env::current_dir()
            .map(|p| p.display().to_string())
            .unwrap_or_else(|_| "unknown".to_string());
        eprintln!("alm compiler error: Failed to read source file '{source_path}'");
        eprintln!("  Current directory: {cwd}");
        eprintln!("  System error: {e}");
        std::process::exit(1);
    });

    let mut tokens = Vec::new();
    let mut offsets = Vec::new();
    let mut front_diagnostics = Vec::new();
    let mut lexer = lexer::Token::lexer(&source);
    loop {
        match lexer.next() {
            Some(Ok(token)) => {
                offsets.push(lexer.span().start);
                tokens.push(token);
            }
            Some(Err(_)) => {
                let line = 1 + source.as_bytes()[..lexer.span().start]
                    .iter()
                    .filter(|b| **b == b'\n')
                    .count();
                front_diagnostics.push(format!("line {line}: Syntax Error: Lexer error"));
                break;
            }
            None => break,
        }
    }

    let mut parser = parser::Parser::new(tokens.into_iter().zip(offsets).collect(), &source);
    let ast = parser.parse_program();
    front_diagnostics.extend(parser.diagnostics);

    if !front_diagnostics.is_empty() {
        fail_build(&front_diagnostics);
    }

    if uses_ffi(&ast) && !standalone {
        eprintln!(
            "alm compiler error: the ffi surface (require(\"ffi\") / ffi.load / lib.sym) is \
             --exe-only — rebuild with --exe; a shared object loading shared objects is not \
             acyclic destiny"
        );
        std::process::exit(1);
    }

    let ctx = analysis::build_context(&ast);

    // one walk: the shape analyzer's recorded pass IS the checker (the
    // fold) — analyze returns the complete fact set plus diagnostics
    let shape = shape::analyze(&ctx);

    if !shape.diagnostics.is_empty() {
        fail_build(&shape.diagnostics);
    }

    let mut ir_lowerer = lowerer::IrLowerer::new(&shape, ctx.stmt_locs);
    let mut ir_program = ir_lowerer.lower_program(&ast);

    if !ir_lowerer.diagnostics.is_empty() {
        fail_build(&ir_lowerer.diagnostics);
    }

    ir_program.source_file =
        std::fs::canonicalize(source_path).unwrap_or_else(|_| source_path.into());

    let arg_used = references_arg(&ast);
    if standalone {
        ir_program.entry = ir::EntryKind::Exe { args: arg_used };
    }

    let llvm_ir = match backend::generate_llvm_ir(&ir_program) {
        Ok(ir) => ir,
        Err(diagnostics) => fail_build(&diagnostics),
    };
    let out_dir = std::path::Path::new(&output_file)
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_else(|| ".".to_string());
    std::fs::create_dir_all(&out_dir).expect("Failed to create output directory");
    let stem = std::path::Path::new(&output_file)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("alm_out");
    let ll_name = format!("{out_dir}/{stem}.ll");
    let _ = std::fs::remove_file(&ll_name);
    std::fs::remove_file(&output_file).ok();
    std::fs::write(&ll_name, llvm_ir).expect("Failed to write LLVM IR");

    let profile = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let runtime = format!(
        "{}/target/{}/libalm_rt.a",
        env!("CARGO_MANIFEST_DIR"),
        profile
    );
    // the C11 async substrate lives next to the runtime archive; every
    // artifact links it so process-wide alm state (exec registry, trace
    // plate, exit report) has exactly one home per process
    let async_dir = std::path::Path::new(&runtime)
        .parent()
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_else(|| ".".into());

    let link_kind = if standalone {
        "executable"
    } else {
        "Shared library"
    };
    let mut link = std::process::Command::new("clang");
    link.arg(if debug { "-O0" } else { "-O3" })
        .arg("-Wno-override-module")
        .arg("-fuse-ld=lld")
        .arg("-g");
    if debug {
        link.arg("-fno-omit-frame-pointer").arg("-fno-inline");
    }
    if !standalone {
        link.arg("-shared").arg("-fPIC");
    }
    if verbose {
        link.stdout(Stdio::inherit()).stderr(Stdio::inherit());
    }
    let status = link
        .arg(&ll_name)
        .arg(&runtime)
        .arg(format!("-L{async_dir}"))
        .arg("-lalm_async")
        .arg(format!("-Wl,-rpath,{async_dir}"))
        .arg("-Wl,-rpath,$ORIGIN")
        .arg("-lpthread")
        .arg("-ldl")
        .arg("-lm")
        .arg("-o")
        .arg(&output_file)
        .status()
        .expect("Failed to execute clang");

    if !status.success() {
        panic!("Clang failed to assemble and link the {link_kind}.");
    }
    println!("Success! {link_kind} written to {output_file}");
    alm_rt::trace::compiler_trace_signal(alm_rt::trace::TRACE_COMPILED);
    eprintln!("ALM_TRACE: slot 0 — compiled ok");

    if standalone {
        return;
    }

    let words: Vec<String> = args[idx + 1..].to_vec();
    if let Err(e) = unsafe { run_boundary(&words, &output_file) } {
        eprintln!("alm host error: {e}");
        std::process::exit(1);
    }
}

fn arg_kind_words(kind: i32) -> &'static str {
    match kind {
        alm_rt::rt::ALM_ARG_FLOAT => "numbers (64-bit floats)",
        alm_rt::rt::ALM_ARG_BOOL => "booleans ('true'/'false')",
        alm_rt::rt::ALM_ARG_STRING => "strings (any word)",
        alm_rt::rt::ALM_ARG_ANY => "int, float, bool, or string words",
        _ => "integers (64-bit)",
    }
}

fn arg_kind_table(kind: i32) -> &'static str {
    match kind {
        alm_rt::rt::ALM_ARG_FLOAT => "Table<Float>",
        alm_rt::rt::ALM_ARG_BOOL => "Table<Boolean>",
        alm_rt::rt::ALM_ARG_STRING => "Table<String>",
        alm_rt::rt::ALM_ARG_ANY => "Table<Any>",
        _ => "Table<Integer>",
    }
}
