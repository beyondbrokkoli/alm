use crate::ast::StaticType;
use crate::ir::{
    BlockId, Bool, CellGet, CellSet, CellSetFast, CmpRegs, DbgBind, EntryKind, Instruction, Int,
    IrProgram, MoveRegs, NumRegs, NumRegsRhs, PackRegs, PhiRegs, Ptr, Reg, RegKind, Repr,
    SourceLoc, Terminator, UnaryNum,
};
use crate::shape::LayoutVerdict;
use glm_rt::trace;
use std::collections::HashMap;
use std::path::Path;

fn elem_size(ty: &StaticType) -> u32 {
    match ty {
        StaticType::Boolean => 1,
        StaticType::Unknown(_) => 1,
        StaticType::Any => 16,
        _ => 8,
    }
}

fn elem_kind_code(ty: &StaticType) -> u8 {
    match ty {
        StaticType::Integer => glm_rt::rt::GLM_ARG_INT as u8,
        StaticType::Float => glm_rt::rt::GLM_ARG_FLOAT as u8,
        StaticType::Boolean => glm_rt::rt::GLM_ARG_BOOL as u8,
        StaticType::String => glm_rt::rt::GLM_ARG_STRING as u8,
        StaticType::Any => glm_rt::rt::GLM_ARG_ANY as u8,
        StaticType::Table(_) => glm_rt::rt::GLM_ELEM_TABLE,
        _ => glm_rt::rt::GLM_ELEM_UNDECIDED,
    }
}

fn llvm_bytes(bytes: &[u8]) -> String {
    let mut out = String::new();
    for &b in bytes {
        match b {
            b'"' => out.push_str("\\22"),
            b'\\' => out.push_str("\\5C"),
            0x20..=0x7E => out.push(b as char),
            _ => out.push_str(&format!("\\{b:02X}")),
        }
    }
    out
}

const DI_FILE: usize = 3;
const DI_CU: usize = 4;
const DI_SP: usize = 5;
const DI_FN_TY: usize = 6;
const DI_PTR_TY: usize = 7;
const DI_I64_TY: usize = 8;
const DI_F64_TY: usize = 9;
const DI_BOOL_TY: usize = 10;
const DI_ANY_TY: usize = 11;
const DI_FLAGS: usize = 12;
const DI_VAR_BASE: usize = 15;

struct DebugMeta {
    defs: String,
    next: usize,
    locs: HashMap<(u32, u32), usize>,
    vars: HashMap<String, usize>,
}

impl DebugMeta {
    fn new(source: &Path) -> Option<Self> {
        let file_name = source.file_name()?.to_string_lossy().into_owned();
        let dir = source
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or_else(|| Path::new("."))
            .to_string_lossy()
            .into_owned();
        let mut defs = String::new();
        defs.push_str(&format!(
            "!{DI_FILE} = !DIFile(filename: \"{}\", directory: \"{}\")\n",
            llvm_bytes(file_name.as_bytes()),
            llvm_bytes(dir.as_bytes())
        ));
        defs.push_str(&format!(
            "!{DI_CU} = distinct !DICompileUnit(language: DW_LANG_C99, file: !{DI_FILE}, \
             producer: \"glm\", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, \
             enums: !{{}})\n"
        ));
        defs.push_str(&format!(
            "!{DI_SP} = distinct !DISubprogram(name: \"glm_exec\", linkageName: \"glm_exec\", \
             scope: !{DI_FILE}, file: !{DI_FILE}, line: 1, type: !{DI_FN_TY}, scopeLine: 1, \
             spFlags: DISPFlagDefinition, unit: !{DI_CU})\n"
        ));
        defs.push_str(&format!(
            "!{DI_FN_TY} = !DISubroutineType(types: !{{null, !{DI_PTR_TY}, !{DI_PTR_TY}}})\n\
             !{DI_PTR_TY} = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)\n\
             !{DI_I64_TY} = !DIBasicType(name: \"i64\", size: 64, encoding: DW_ATE_signed)\n\
             !{DI_F64_TY} = !DIBasicType(name: \"f64\", size: 64, encoding: DW_ATE_float)\n\
             !{DI_BOOL_TY} = !DIBasicType(name: \"bool\", size: 8, encoding: DW_ATE_boolean)\n\
             !{DI_ANY_TY} = !DIBasicType(name: \"any\", size: 128, encoding: DW_ATE_unsigned)\n"
        ));
        defs.push_str(&format!(
            "!{DI_FLAGS} = !{{i32 2, !\"Dwarf Version\", i32 4}}\n\
             !{} = !{{i32 2, !\"Debug Info Version\", i32 3}}\n\
             !{} = !{{i32 2, !\"PIC Level\", i32 2}}\n",
            DI_FLAGS + 1,
            DI_FLAGS + 2
        ));
        Some(Self {
            defs,
            next: DI_VAR_BASE,
            locs: HashMap::new(),
            vars: HashMap::new(),
        })
    }

    fn loc_node(&mut self, loc: SourceLoc) -> usize {
        let key = (loc.line, loc.col);
        if let Some(&id) = self.locs.get(&key) {
            return id;
        }
        let id = self.next;
        self.next += 1;
        self.defs.push_str(&format!(
            "!{id} = distinct !DILocation(line: {}, column: {}, scope: !{DI_SP})\n",
            loc.line, loc.col
        ));
        self.locs.insert(key, id);
        id
    }

    fn var_node(&mut self, bind: &DbgBind) -> usize {
        if let Some(&id) = self.vars.get(&bind.name) {
            return id;
        }
        let id = self.next;
        self.next += 1;
        let ty = match bind.kind {
            RegKind::Int => DI_I64_TY,
            RegKind::Float => DI_F64_TY,
            RegKind::Bool => DI_BOOL_TY,
            RegKind::Any => DI_ANY_TY,
            RegKind::Ptr => DI_PTR_TY,
        };
        let arg = bind
            .param
            .map(|n| format!("arg: {n}, "))
            .unwrap_or_default();
        let line = bind.loc.map(|l| l.line).unwrap_or(0);
        self.defs.push_str(&format!(
            "!{id} = !DILocalVariable(name: \"{}\", {arg}scope: !{DI_SP}, file: !{DI_FILE}, \
             line: {line}, type: !{ty})\n",
            llvm_bytes(bind.name.as_bytes())
        ));
        self.vars.insert(bind.name.clone(), id);
        id
    }

    fn tail(&self) -> String {
        format!(
            "\n!llvm.dbg.cu = !{{!{DI_CU}}}\n\
             !llvm.module.flags = !{{!{DI_FLAGS}, !{}, !{}}}\n{}",
            DI_FLAGS + 1,
            DI_FLAGS + 2,
            self.defs
        )
    }
}

fn dbg_ty(kind: RegKind) -> &'static str {
    match kind {
        RegKind::Int => "i64",
        RegKind::Float => "double",
        RegKind::Bool => "i1",
        RegKind::Any => "i128",
        RegKind::Ptr => "ptr",
    }
}

fn attach_dbg(code: &mut String, start: usize, node: usize) {
    let added = code[start..].to_string();
    code.truncate(start);
    for line in added.split_inclusive('\n') {
        if line.starts_with("  ") && !line.trim().is_empty() {
            code.push_str(line.trim_end_matches('\n'));
            code.push_str(&format!(", !dbg !{node}\n"));
        } else {
            code.push_str(line);
        }
    }
}

fn flush_binds(
    code: &mut String,
    needs_decl: &mut bool,
    dbg: &mut Option<DebugMeta>,
    binds: &mut Vec<&DbgBind>,
) {
    for bind in binds.drain(..) {
        let Some(d) = dbg else { continue };
        *needs_decl = true;
        let var = d.var_node(bind);
        let loc = bind.loc.unwrap_or(SourceLoc { line: 1, col: 1 });
        let dbg_loc = d.loc_node(loc);
        code.push_str(&format!(
            "  call void @llvm.dbg.value(metadata {} %v{}, metadata !{}, \
             metadata !DIExpression()), !dbg !{}\n",
            dbg_ty(bind.kind),
            bind.reg,
            var,
            dbg_loc
        ));
    }
}

struct SeamPlan {
    numbers: Vec<Vec<Option<usize>>>,
}

impl SeamPlan {
    fn number(&self, block: BlockId, ii: usize) -> usize {
        self.numbers[block][ii].expect("the seam plan numbered every table-seam instruction")
    }
}

fn plan_seams(program: &IrProgram) -> SeamPlan {
    let mut numbers: Vec<Vec<Option<usize>>> = program
        .blocks
        .iter()
        .map(|b| vec![None; b.instrs.len()])
        .collect();
    let mut probe = 0usize;
    for block in &program.blocks {
        for (ii, instr) in block.instrs.iter().enumerate() {
            match instr {
                Instruction::TableSetFast { .. } => {
                    assert!(
                        ii == block.instrs.len() - 1,
                        "a fast store must end its block (the lowerer \
                         owns the continuation) — block {} carries one \
                         at index {} that is not last",
                        block.id,
                        ii
                    );
                    numbers[block.id][ii] = Some(probe);
                    probe += 1;
                }
                Instruction::TableGet { .. } | Instruction::TableSet { .. } => {
                    numbers[block.id][ii] = Some(probe);
                    probe += 1;
                }
                _ => {}
            }
        }
    }
    SeamPlan { numbers }
}

fn assert_labels_closed(ir: &str) {
    let mut defined: Vec<&str> = Vec::new();
    let mut referenced: Vec<&str> = Vec::new();
    for line in ir.lines() {
        if let Some(name) = line.strip_suffix(':')
            && is_label_name(name)
        {
            defined.push(name);
        } else if line.starts_with(' ') {
            scan_label_refs(line, &mut referenced);
        }
    }
    for name in &referenced {
        assert!(
            defined.contains(name),
            "IR emitter label desync: a br/phi names block '{name}', \
             which the module never emits — the emitters and the block \
             model disagree (see SeamPlan in backend.rs)"
        );
    }
}

fn is_label_name(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' || c == '$' || c == '.' => {}
        _ => return false,
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '.')
}

fn is_label_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '.'
}

fn scan_label_refs<'a>(line: &'a str, out: &mut Vec<&'a str>) {
    let mut rest = line;
    while let Some(i) = rest.find("label %") {
        rest = &rest[i + "label %".len()..];
        let end = rest.find(|c: char| !is_label_char(c)).unwrap_or(rest.len());
        out.push(&rest[..end]);
        rest = &rest[end..];
    }
    let mut rest = line;
    while let Some(i) = rest.find(", %") {
        rest = &rest[i + ", %".len()..];
        let end = rest.find(|c: char| !is_label_char(c)).unwrap_or(rest.len());
        if rest[end..].starts_with(" ]") {
            out.push(&rest[..end]);
        }
        rest = &rest[end..];
    }
}

pub fn generate_llvm_ir(program: &IrProgram) -> Result<String, Vec<String>> {
    let mut globals = String::new();
    let mut dbg = DebugMeta::new(&program.source_file);
    let mut needs_dbg_value_decl = false;
    let mut str_pool: HashMap<&str, String> = HashMap::new();
    let mut str_order: Vec<String> = Vec::new();
    let mut str_idx = 0;
    let mut needs_floor_decl = false;
    let mut needs_div_guard = false;
    let mut needs_tbl_new_decl = false;
    let mut needs_tbl_reserve_decl = false;
    let mut needs_tbl_free_decl = false;
    let mut needs_tbl_free_except_decl = false;
    let mut needs_tbl_free_except_n_decl = false;
    let mut needs_tbl_get_decl = false;
    let mut needs_tbl_set_decl = false;
    let mut needs_tbl_get_any_decl = false;
    let mut needs_tbl_set_any_decl = false;
    let mut needs_str_len_decl = false;
    let mut needs_sys_alloc_count_decl = false;
    let mut needs_sys_exec_count_decl = false;
    let mut needs_coro_decls = false;
    let mut needs_ffi_load_decl = false;
    let mut needs_ffi_arg_kind_decl = false;
    let mut needs_ffi_call_decl = false;
    let mut needs_any_print_decl = false;
    let mut needs_any_eq_decl = false;
    let mut needs_any_len_decl = false;
    let mut needs_tbl_len_decl = false;
    let mut needs_any_from: u8 = 0;
    let mut needs_hdr_md = false;
    let mut ks = 0usize;
    let seam_plan = plan_seams(program);

    let mut allocas = String::new();
    let mut code = String::new();

    for block in &program.blocks {
        code.push_str(&format!("\nb{}:\n", block.id));

        let mut pending_binds: Vec<&DbgBind> = Vec::new();

        for (ii, instr) in block.instrs.iter().enumerate() {
            if !matches!(instr, Instruction::Phi(_)) {
                flush_binds(
                    &mut code,
                    &mut needs_dbg_value_decl,
                    &mut dbg,
                    &mut pending_binds,
                );
            }
            let start = code.len();
            match instr {
                Instruction::LoadInt { target, val } => {
                    code.push_str(&format!("  %v{} = add i64 0, {}\n", target.id, val))
                }
                Instruction::LoadFloat { target, val } => {
                    code.push_str(&format!("  %v{} = fadd double 0.0, {:?}\n", target.id, val))
                }
                Instruction::LoadBool { target, val } => code.push_str(&format!(
                    "  %v{} = or i1 0, {}\n",
                    target.id,
                    if *val { 1 } else { 0 }
                )),
                Instruction::LoadAnyZero { target } => {
                    code.push_str(&format!("  %v{} = add i128 0, 0\n", target.id))
                }
                Instruction::LoadString { target, val } => {
                    let g = match str_pool.get(val.as_str()) {
                        Some(name) => {
                            trace::compiler_trace_signal(trace::TRACE_STR_POOL_HIT);
                            name.clone()
                        }
                        None => {
                            let g = format!("@.str.{}", str_idx);
                            str_idx += 1;
                            str_order.push(g.clone());
                            globals.push_str(&format!(
                                "{} = private unnamed_addr constant [{} x i8] c\"{}\\00\"\n",
                                g,
                                val.len() + 1,
                                llvm_bytes(val.as_bytes())
                            ));
                            str_pool.insert(val.as_str(), g.clone());
                            g
                        }
                    };
                    code.push_str(&format!(
                        "  %v{} = getelementptr inbounds [{} x i8], ptr {}, i64 0, i64 0\n",
                        target.id,
                        val.len() + 1,
                        g
                    ));
                }
                Instruction::StrLen { target, s } => {
                    needs_str_len_decl = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @glm_str_len(ptr %v{})\n",
                        target.id, s.id
                    ));
                }
                Instruction::AnyLen { target, source } => {
                    needs_any_len_decl = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @glm_any_len(i128 %v{})\n",
                        target.id, source.id
                    ));
                }
                Instruction::TableLen { target, table } => {
                    needs_tbl_len_decl = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @glm_tbl_len(ptr %v{})\n",
                        target.id, table.id
                    ));
                }
                Instruction::AnyPack { target, source } => match source {
                    PackRegs::Int(s) => {
                        needs_any_from |= 1;
                        code.push_str(&format!(
                            "  %v{} = call i128 @glm_any_from_int(i64 %v{})\n",
                            target.id, s.id
                        ));
                    }
                    PackRegs::Float(s) => {
                        needs_any_from |= 2;
                        code.push_str(&format!(
                            "  %v{} = call i128 @glm_any_from_float(double %v{})\n",
                            target.id, s.id
                        ));
                    }
                    PackRegs::Bool(s) => {
                        needs_any_from |= 4;
                        code.push_str(&format!(
                            "  %v{t}.bz = zext i1 %v{src} to i8\n  %v{t} = call i128 \
                             @glm_any_from_bool(i8 %v{t}.bz)\n",
                            t = target.id,
                            src = s.id
                        ));
                    }
                    PackRegs::Str(s) => {
                        needs_any_from |= 8;
                        code.push_str(&format!(
                            "  %v{} = call i128 @glm_any_from_str(ptr %v{})\n",
                            target.id, s.id
                        ));
                    }
                },
                Instruction::Move(m) => emit_move(m, &mut code),
                Instruction::LoadNull { target } => {
                    code.push_str(&format!("  %v{} = inttoptr i64 0 to ptr\n", target.id));
                }
                Instruction::BindArgs { target } => {
                    code.push_str(&format!(
                        "  %v{} = getelementptr i8, ptr %args, i64 0\n",
                        target.id
                    ));
                }

                Instruction::TableNew {
                    target,
                    elem,
                    flags,
                } => {
                    trace::compiler_trace_signal(trace::TRACE_OFFLOAD_EMIT);

                    needs_tbl_new_decl = true;
                    needs_hdr_md = true;

                    code.push_str(&format!(
                        "  %v{} = call ptr @glm_tbl_new(i64 {}, i8 {})\n",
                        target.id,
                        elem_size(elem),
                        flags | (elem_kind_code(elem) << 1)
                    ));
                }
                Instruction::TableGet(g) => {
                    emit_cell_get(
                        g,
                        &mut allocas,
                        &mut code,
                        seam_plan.number(block.id, ii),
                        &mut needs_tbl_get_decl,
                        &mut needs_tbl_get_any_decl,
                    );
                }
                Instruction::TableReserve { table, bound } => {
                    needs_tbl_reserve_decl = true;
                    code.push_str(&format!(
                        "  call void @glm_tbl_reserve(ptr %v{}, i64 %v{})\n",
                        table.id, bound.id
                    ));
                }

                Instruction::TableSetFast(s) => {
                    emit_cell_set_fast(
                        s,
                        &mut allocas,
                        &mut code,
                        seam_plan.number(block.id, ii),
                        &mut needs_hdr_md,
                        &mut needs_tbl_set_decl,
                        &mut needs_tbl_set_any_decl,
                    );
                }
                Instruction::TableSet(s) => {
                    emit_cell_set(
                        s,
                        &mut allocas,
                        &mut code,
                        seam_plan.number(block.id, ii),
                        &mut needs_tbl_set_decl,
                        &mut needs_tbl_set_any_decl,
                    );
                }
                Instruction::TableFree { table } => {
                    trace::compiler_trace_signal(trace::TRACE_OFFLOAD_EMIT);

                    needs_tbl_free_decl = true;
                    code.push_str(&format!("  call void @glm_tbl_free(ptr %v{})\n", table.id));
                }
                Instruction::TableFreeExcept { table, keeps } => {
                    trace::compiler_trace_signal(trace::TRACE_OFFLOAD_EMIT);

                    if keeps.len() == 1 {
                        needs_tbl_free_except_decl = true;
                        code.push_str(&format!(
                            "  call void @glm_tbl_free_except(ptr %v{}, ptr %v{})\n",
                            table.id, keeps[0].id
                        ));
                    } else {
                        needs_tbl_free_except_n_decl = true;
                        let f = ks;
                        ks += 1;
                        allocas.push_str(&format!(
                            "  %kf{f} = alloca [{n} x ptr]\n",
                            f = f,
                            n = keeps.len()
                        ));
                        for (i, k) in keeps.iter().enumerate() {
                            code.push_str(&format!(
                                "  store ptr %v{k}, ptr %kf{f}, i64 {i}\n",
                                k = k.id,
                                f = f,
                                i = i
                            ));
                        }
                        code.push_str(&format!(
                            "  call void @glm_tbl_free_except_n(ptr %v{t}, ptr %kf{f}, i64 {n})\n",
                            t = table.id,
                            f = f,
                            n = keeps.len()
                        ));
                    }
                }
                Instruction::SysAllocCount { target } => {
                    needs_sys_alloc_count_decl = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @sys_alloc_count()\n",
                        target.id
                    ));
                }
                Instruction::SysExecCount { target } => {
                    needs_sys_exec_count_decl = true;
                    code.push_str(&format!("  %v{} = call i64 @sys_exec_count()\n", target.id));
                }
                Instruction::CoroCreate { target, lib } => {
                    needs_coro_decls = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @glm_coro_create(ptr %v{})\n",
                        target.id, lib.id
                    ));
                }
                Instruction::CoroResume {
                    target,
                    handle,
                    args,
                } => {
                    needs_coro_decls = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @glm_coro_resume(i64 %v{}, ptr %v{})\n",
                        target.id, handle.id, args.id
                    ));
                }
                Instruction::CoroYield { target, value } => {
                    needs_coro_decls = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @glm_coro_yield(i64 %v{})\n",
                        target.id, value.id
                    ));
                }
                Instruction::CoroStatus { target, handle } => {
                    needs_coro_decls = true;
                    code.push_str(&format!(
                        "  %v{} = call ptr @glm_coro_status(i64 %v{})\n",
                        target.id, handle.id
                    ));
                }
                Instruction::CoroClose { target, handle } => {
                    needs_coro_decls = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @glm_coro_close(i64 %v{})\n",
                        target.id, handle.id
                    ));
                }
                Instruction::FfiLoad { target, path } => {
                    needs_ffi_load_decl = true;
                    code.push_str(&format!(
                        "  %v{} = call ptr @glm_ffi_load(ptr %v{})\n",
                        target.id, path.id
                    ));
                }
                Instruction::FfiArgKind { target, lib } => {
                    needs_ffi_arg_kind_decl = true;
                    code.push_str(&format!(
                        "  %v{} = call i64 @glm_ffi_arg_kind(ptr %v{})\n",
                        target.id, lib.id
                    ));
                }
                Instruction::FfiCall { lib, sym, arg } => {
                    needs_ffi_call_decl = true;
                    let g = match str_pool.get(sym.as_str()) {
                        Some(name) => name.clone(),
                        None => {
                            let g = format!("@.str.{}", str_idx);
                            str_idx += 1;
                            str_order.push(g.clone());
                            globals.push_str(&format!(
                                "{} = private unnamed_addr constant [{} x i8] c\"{}\\00\"\n",
                                g,
                                sym.len() + 1,
                                llvm_bytes(sym.as_bytes())
                            ));
                            str_pool.insert(sym.as_str(), g.clone());
                            g
                        }
                    };
                    code.push_str(&format!(
                        "  call void @glm_ffi_call(ptr %v{}, ptr {}, ptr %v{})\n",
                        lib.id, g, arg.id
                    ));
                }
                Instruction::Add(n) => math_regs(n, "add", "fadd", &mut code),
                Instruction::Sub(n) => math_regs(n, "sub", "fsub", &mut code),
                Instruction::Mul(n) => math_regs(n, "mul", "fmul", &mut code),
                Instruction::Div {
                    target,
                    left,
                    right,
                } => {
                    code.push_str(&format!(
                        "  %v{} = fdiv double %v{}, %v{}\n",
                        target.id, left.id, right.id
                    ));
                }
                Instruction::Sitofp { target, source } => {
                    code.push_str(&format!(
                        "  %v{} = sitofp i64 %v{} to double\n",
                        target.id, source.id
                    ));
                }
                Instruction::IntDiv(n) => {
                    floor_div_regs(n, &mut code, &mut needs_floor_decl, &mut needs_div_guard)
                }
                Instruction::Mod(n) => mod_regs(n, &mut code, &mut needs_div_guard),
                Instruction::Neg(u) => neg_regs(u, &mut code),
                Instruction::Less(c) => {
                    cmp_regs(c, "slt", "olt", &mut code, &mut needs_any_eq_decl)
                }
                Instruction::Leq(c) => cmp_regs(c, "sle", "ole", &mut code, &mut needs_any_eq_decl),
                Instruction::Geq(c) => cmp_regs(c, "sge", "oge", &mut code, &mut needs_any_eq_decl),
                Instruction::Eq(c) => cmp_regs(c, "eq", "oeq", &mut code, &mut needs_any_eq_decl),
                Instruction::Not { target, source } => {
                    code.push_str(&format!("  %v{} = xor i1 %v{}, 1\n", target.id, source.id));
                }
                Instruction::Phi(PhiRegs::Int { target, args }) => {
                    emit_phi(target, args, &mut code)
                }
                Instruction::Phi(PhiRegs::Float { target, args }) => {
                    emit_phi(target, args, &mut code)
                }
                Instruction::Phi(PhiRegs::Bool { target, args }) => {
                    emit_phi(target, args, &mut code)
                }
                Instruction::Phi(PhiRegs::Ptr { target, args }) => {
                    emit_phi(target, args, &mut code)
                }
                Instruction::Phi(PhiRegs::Any { target, args }) => {
                    emit_phi(target, args, &mut code)
                }
                Instruction::Print { operands } => {
                    for (i, (r, ty)) in operands.iter().enumerate() {
                        if i > 0 {
                            code.push_str("  call void @glm_print_sep()\n");
                        }
                        let (r, ty) = (*r, ty);
                        match ty {
                            StaticType::Integer => {
                                code.push_str(&format!("  call void @glm_print_int(i64 %v{})\n", r))
                            }
                            StaticType::Float => code.push_str(&format!(
                                "  call void @glm_print_float(double %v{})\n",
                                r
                            )),
                            StaticType::Boolean => {
                                code.push_str(&format!("  call void @glm_print_bool(i1 %v{})\n", r))
                            }
                            StaticType::String => code
                                .push_str(&format!("  call void @glm_print_string(ptr %v{})\n", r)),
                            StaticType::Any => {
                                needs_any_print_decl = true;
                                code.push_str(&format!(
                                    "  call void @glm_any_print(i128 %v{})\n",
                                    r
                                ));
                            }
                            StaticType::Table(_) => {
                                return Err(vec![
                                    "Type Error: tables cannot be printed".to_string(),
                                ]);
                            }
                            StaticType::Ffi | StaticType::FfiLib | StaticType::Coro => {
                                return Err(vec![
                                    "Type Error: the module surfaces cannot be printed".to_string(),
                                ]);
                            }
                            StaticType::Unknown(_) => {
                                code.push_str("  call void @glm_print_int(i64 0)\n")
                            }
                        }
                    }
                    code.push_str("  call void @glm_print_nl()\n");
                }
            }
            if let Some(loc) = block.locs.get(ii).copied().flatten()
                && let Some(d) = &mut dbg
            {
                let node = d.loc_node(loc);
                attach_dbg(&mut code, start, node);
            }
            pending_binds.extend(block.dbg_values.iter().filter(|b| b.after == ii));
        }

        if let Some(Instruction::TableSetFast(s)) = block.instrs.last() {
            let cont = s.cont();
            assert!(
                matches!(block.terminator, Some(Terminator::Jump(b)) if b == cont),
                "a fast store's block must jump to its own continuation — \
                 block {} ends in a fast store but does not jump to b{}",
                block.id,
                cont
            );
            assert!(
                pending_binds.is_empty(),
                "a bind banked past a fast store would emit past its \
                 terminator — block {}",
                block.id
            );
        } else {
            flush_binds(
                &mut code,
                &mut needs_dbg_value_decl,
                &mut dbg,
                &mut pending_binds,
            );
            let term_start = code.len();
            match &block.terminator {
                Some(Terminator::Jump(b)) => code.push_str(&format!("  br label %b{}\n", b)),
                Some(Terminator::Branch {
                    cond,
                    true_block,
                    false_block,
                }) => code.push_str(&format!(
                    "  br i1 %v{}, label %b{}, label %b{}\n",
                    cond.id, true_block, false_block
                )),
                Some(Terminator::Return(val)) => {
                    code.push_str(&format!("  ret ptr %v{}\n", val.id))
                }
                Some(Terminator::Halt) | None => code.push_str("  ret ptr null\n"),
            }
            if let Some(loc) = block.term_loc
                && let Some(d) = &mut dbg
            {
                let node = d.loc_node(loc);
                attach_dbg(&mut code, term_start, node);
            }
        }
    }

    let mut out = String::from(
        "declare void @glm_print_int(i64)\n\
         declare void @glm_print_float(double)\n\
         declare void @glm_print_bool(i1)\n\
         declare void @glm_print_string(ptr)\n\
         declare void @glm_print_sep()\n\
         declare void @glm_print_nl()\n\n\
         ",
    );
    out.push_str(if dbg.is_some() {
        "define ptr @glm_exec(ptr %args) !dbg !5 {\nentry:\n"
    } else {
        "define ptr @glm_exec(ptr %args) {\nentry:\n"
    });
    out.push_str(&allocas);
    out.push_str("  br label %b0\n");
    out.push_str(&code);
    out.push_str("}\n");

    let arg_kind = match program.boundary_elem {
        Some(elem) => glm_rt::rt::arg_kind_of(&elem),
        None => glm_rt::rt::GLM_ARG_NONE,
    };
    out.push_str(&format!(
        "\ndefine i32 @glm_arg_kind() {{\n\
         entry:\n\
           ret i32 {arg_kind}\n\
         }}\n"
    ));

    let mut needs_exec_main_decl = false;
    if let EntryKind::Exe { args } = program.entry {
        if args {
            out.push_str(&format!(
                "\ndefine i32 @main(i32 %argc, ptr %argv) {{\n\
                 entry:\n\
                   %rc = call i32 @glm_exec_main(i32 %argc, ptr %argv, i32 {arg_kind}, ptr @glm_exec)\n\
                   ret i32 %rc\n\
                 }}\n"
            ));
            needs_exec_main_decl = true;
        } else {
            out.push_str(
                "\ndefine i32 @main() {\n\
                 entry:\n\
                   %r = call ptr @glm_exec(ptr null)\n\
                   call void @glm_tbl_free(ptr %r)\n\
                   ret i32 0\n\
                 }\n",
            );
            needs_tbl_free_decl = true;
        }
    }

    let mut registry = String::new();
    let str_carrying = matches!(
        program.boundary_elem,
        Some(glm_rt::GlmElem::String | glm_rt::GlmElem::Any)
    );
    if str_carrying && !str_order.is_empty() {
        trace::compiler_trace_signal(trace::TRACE_STRTAB_EMIT);
        let ptrs: Vec<String> = str_order.iter().map(|g| format!("ptr {g}")).collect();
        registry.push_str(&format!(
            "@.glm_strtab = global [{} x ptr] [{}]\n",
            ptrs.len(),
            ptrs.join(", ")
        ));
        registry.push_str(&format!(
            "\ndefine internal void @.glm_strreg() {{\n\
             entry:\n\
               call void @glm_str_register(ptr @.glm_strtab, i64 {})\n\
               ret void\n\
             }}\n\
             @llvm.global_ctors = appending global \
             [1 x {{ i32, ptr, ptr }}] \
             [{{ i32, ptr, ptr }} {{ i32 65535, ptr @.glm_strreg, ptr null }}]\n",
            ptrs.len()
        ));
    }

    let mut head = String::new();
    if needs_floor_decl {
        head.push_str("declare double @llvm.floor.f64(double)\n");
    }
    if needs_tbl_new_decl {
        head.push_str("declare ptr @glm_tbl_new(i64, i8)\n");
    }
    if needs_tbl_reserve_decl {
        head.push_str("declare void @glm_tbl_reserve(ptr, i64)\n");
    }
    if needs_tbl_free_decl {
        head.push_str("declare void @glm_tbl_free(ptr)\n");
    }
    if needs_tbl_free_except_decl {
        head.push_str("declare void @glm_tbl_free_except(ptr, ptr)\n");
    }
    if needs_tbl_free_except_n_decl {
        head.push_str("declare void @glm_tbl_free_except_n(ptr, ptr, i64)\n");
    }
    if needs_tbl_get_decl {
        head.push_str("declare void @glm_tbl_get(ptr, i64, ptr, i64)\n");
    }
    if needs_tbl_set_decl {
        head.push_str("declare void @glm_tbl_set(ptr, i64, ptr)\n");
    }
    if needs_tbl_get_any_decl {
        head.push_str("declare i128 @glm_tbl_get_any(ptr, i64)\n");
    }
    if needs_tbl_set_any_decl {
        head.push_str("declare void @glm_tbl_set_any(ptr, i64, i128)\n");
    }
    if needs_str_len_decl {
        head.push_str("declare i64 @glm_str_len(ptr)\n");
    }
    if needs_sys_alloc_count_decl {
        head.push_str("declare i64 @sys_alloc_count()\n");
    }
    if needs_sys_exec_count_decl {
        head.push_str("declare i64 @sys_exec_count()\n");
    }
    if needs_coro_decls {
        head.push_str("declare i64 @glm_coro_create(ptr)\n");
        head.push_str("declare i64 @glm_coro_resume(i64, ptr)\n");
        head.push_str("declare i64 @glm_coro_yield(i64)\n");
        head.push_str("declare ptr @glm_coro_status(i64)\n");
        head.push_str("declare i64 @glm_coro_close(i64)\n");
    }
    if needs_ffi_load_decl {
        head.push_str("declare ptr @glm_ffi_load(ptr)\n");
    }
    if needs_ffi_arg_kind_decl {
        head.push_str("declare i64 @glm_ffi_arg_kind(ptr)\n");
    }
    if needs_ffi_call_decl {
        head.push_str("declare void @glm_ffi_call(ptr, ptr, ptr)\n");
    }
    if needs_any_print_decl {
        head.push_str("declare void @glm_any_print(i128)\n");
    }
    if needs_any_eq_decl {
        head.push_str("declare i32 @glm_any_eq(i128, i128)\n");
    }
    if needs_any_len_decl {
        head.push_str("declare i64 @glm_any_len(i128)\n");
    }
    if needs_tbl_len_decl {
        head.push_str("declare i64 @glm_tbl_len(ptr)\n");
    }
    if needs_any_from & 1 != 0 {
        head.push_str("declare i128 @glm_any_from_int(i64)\n");
    }
    if needs_any_from & 2 != 0 {
        head.push_str("declare i128 @glm_any_from_float(double)\n");
    }
    if needs_any_from & 4 != 0 {
        head.push_str("declare i128 @glm_any_from_bool(i8)\n");
    }
    if needs_any_from & 8 != 0 {
        head.push_str("declare i128 @glm_any_from_str(ptr)\n");
    }
    if needs_dbg_value_decl {
        head.push_str("declare void @llvm.dbg.value(metadata, metadata, metadata)\n");
    }
    if needs_div_guard {
        head.push_str("declare void @glm_div_zero_guard(i64)\n");
    }
    if !registry.is_empty() {
        head.push_str("declare void @glm_str_register(ptr, i64)\n");
    }
    if needs_exec_main_decl {
        head.push_str("declare i32 @glm_exec_main(i32, ptr, i32, ptr)\n");
    }

    let mut anchor = String::new();
    /* unconditional for every .so: ANY module can be spawned as a
     * coroutine, and the coro thread wrapper dlsym's glm_tbl_new/set/free
     * to build the boundary table on the worker thread — the anchor keeps
     * the full runtime surface exported even when the module's own IR
     * never references it (the linker would drop the unreferenced archive
     * members otherwise). Each declare is emitted only when the module's
     * own needs_* flag hasn't already declared it (LLVM refuses
     * redeclaration); glm_str_intern has no needs flag — only the anchor
     * and the .init_array registry ever reference it. */
    if matches!(program.entry, EntryKind::Lib) {
        if !needs_tbl_new_decl {
            anchor.push_str("declare ptr @glm_tbl_new(i64, i8)\n");
        }
        if !needs_tbl_set_decl {
            anchor.push_str("declare void @glm_tbl_set(ptr, i64, ptr)\n");
        }
        if !needs_tbl_get_decl {
            anchor.push_str("declare void @glm_tbl_get(ptr, i64, ptr, i64)\n");
        }
        if !needs_tbl_free_decl {
            anchor.push_str("declare void @glm_tbl_free(ptr)\n");
        }
        anchor.push_str(concat!(
            "declare ptr @glm_str_intern(ptr, i64)\n",
            "@.glm_rt_anchor = internal constant [5 x i64] [\n",
            "  i64 ptrtoint (ptr @glm_tbl_new to i64),\n",
            "  i64 ptrtoint (ptr @glm_tbl_set to i64),\n",
            "  i64 ptrtoint (ptr @glm_tbl_get to i64),\n",
            "  i64 ptrtoint (ptr @glm_tbl_free to i64),\n",
            "  i64 ptrtoint (ptr @glm_str_intern to i64)\n",
            "]\n",
            "@llvm.compiler.used = appending global [1 x ptr] [ptr @.glm_rt_anchor]\n",
        ));
    }

    let md = if needs_hdr_md {
        "\n!0 = !{!1}\n\
         !1 = distinct !{!\"glm_table_header\", !2}\n\
         !2 = distinct !{!\"glm_table\"}\n"
            .to_string()
    } else {
        String::new()
    };
    let dbg_tail = dbg.map(|d| d.tail()).unwrap_or_default();
    let ir = format!(
        "{}{}{}{}{}{}{}",
        globals, registry, head, anchor, out, md, dbg_tail
    );
    assert_labels_closed(&ir);
    Ok(ir)
}

fn emit_move(m: &MoveRegs, code: &mut String) {
    match m {
        MoveRegs::Int { target, source } => Repr::emit_move(target, source, code),
        MoveRegs::Float { target, source } => Repr::emit_move(target, source, code),
        MoveRegs::Bool { target, source } => Repr::emit_move(target, source, code),
        MoveRegs::Str { target, source } => Repr::emit_move(target, source, code),
        MoveRegs::Ptr { target, source } => Repr::emit_move(target, source, code),
        MoveRegs::Byte { target, source } => Repr::emit_move(target, source, code),
        MoveRegs::Any { target, source } => Repr::emit_move(target, source, code),
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_cell_get(
    g: &CellGet,
    allocas: &mut String,
    code: &mut String,
    seam: usize,
    needs_tbl_get_decl: &mut bool,
    needs_tbl_get_any_decl: &mut bool,
) {
    match g {
        CellGet::Int {
            target,
            table,
            index,
        } => emit_table_get(
            target,
            table,
            index,
            allocas,
            code,
            seam,
            needs_tbl_get_decl,
            needs_tbl_get_any_decl,
        ),
        CellGet::Float {
            target,
            table,
            index,
        } => emit_table_get(
            target,
            table,
            index,
            allocas,
            code,
            seam,
            needs_tbl_get_decl,
            needs_tbl_get_any_decl,
        ),
        CellGet::Bool {
            target,
            table,
            index,
        } => emit_table_get(
            target,
            table,
            index,
            allocas,
            code,
            seam,
            needs_tbl_get_decl,
            needs_tbl_get_any_decl,
        ),
        CellGet::Ptr {
            target,
            table,
            index,
        } => emit_table_get(
            target,
            table,
            index,
            allocas,
            code,
            seam,
            needs_tbl_get_decl,
            needs_tbl_get_any_decl,
        ),
        CellGet::Byte {
            target,
            table,
            index,
        } => emit_table_get(
            target,
            table,
            index,
            allocas,
            code,
            seam,
            needs_tbl_get_decl,
            needs_tbl_get_any_decl,
        ),
        CellGet::Any {
            target,
            table,
            index,
        } => emit_table_get(
            target,
            table,
            index,
            allocas,
            code,
            seam,
            needs_tbl_get_decl,
            needs_tbl_get_any_decl,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_cell_set_fast(
    s: &CellSetFast,
    allocas: &mut String,
    code: &mut String,
    seam: usize,
    needs_hdr_md: &mut bool,
    needs_tbl_set_decl: &mut bool,
    needs_tbl_set_any_decl: &mut bool,
) {
    match s {
        CellSetFast::Int {
            table,
            index,
            value,
            layout,
            cont,
        } => emit_table_set_fast(
            table,
            index,
            value,
            layout,
            *cont,
            allocas,
            code,
            seam,
            needs_hdr_md,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSetFast::Float {
            table,
            index,
            value,
            layout,
            cont,
        } => emit_table_set_fast(
            table,
            index,
            value,
            layout,
            *cont,
            allocas,
            code,
            seam,
            needs_hdr_md,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSetFast::Bool {
            table,
            index,
            value,
            layout,
            cont,
        } => emit_table_set_fast(
            table,
            index,
            value,
            layout,
            *cont,
            allocas,
            code,
            seam,
            needs_hdr_md,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSetFast::Ptr {
            table,
            index,
            value,
            layout,
            cont,
        } => emit_table_set_fast(
            table,
            index,
            value,
            layout,
            *cont,
            allocas,
            code,
            seam,
            needs_hdr_md,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSetFast::Byte {
            table,
            index,
            value,
            layout,
            cont,
        } => emit_table_set_fast(
            table,
            index,
            value,
            layout,
            *cont,
            allocas,
            code,
            seam,
            needs_hdr_md,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSetFast::Any {
            table,
            index,
            value,
            layout,
            cont,
        } => emit_table_set_fast(
            table,
            index,
            value,
            layout,
            *cont,
            allocas,
            code,
            seam,
            needs_hdr_md,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_cell_set(
    s: &CellSet,
    allocas: &mut String,
    code: &mut String,
    seam: usize,
    needs_tbl_set_decl: &mut bool,
    needs_tbl_set_any_decl: &mut bool,
) {
    match s {
        CellSet::Int {
            table,
            index,
            value,
        } => emit_table_set(
            table,
            index,
            value,
            allocas,
            code,
            seam,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSet::Float {
            table,
            index,
            value,
        } => emit_table_set(
            table,
            index,
            value,
            allocas,
            code,
            seam,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSet::Bool {
            table,
            index,
            value,
        } => emit_table_set(
            table,
            index,
            value,
            allocas,
            code,
            seam,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSet::Ptr {
            table,
            index,
            value,
        } => emit_table_set(
            table,
            index,
            value,
            allocas,
            code,
            seam,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSet::Byte {
            table,
            index,
            value,
        } => emit_table_set(
            table,
            index,
            value,
            allocas,
            code,
            seam,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
        CellSet::Any {
            table,
            index,
            value,
        } => emit_table_set(
            table,
            index,
            value,
            allocas,
            code,
            seam,
            needs_tbl_set_decl,
            needs_tbl_set_any_decl,
        ),
    }
}

fn math_regs(n: &NumRegs, int_op: &str, flt_op: &str, code: &mut String) {
    match n {
        NumRegs::Int {
            target,
            left,
            right,
        } => math_op(target, left, right, int_op, flt_op, code),
        NumRegs::Float {
            target,
            left,
            right,
        } => math_op(target, left, right, int_op, flt_op, code),
    }
}

fn floor_div_regs(
    n: &NumRegsRhs,
    code: &mut String,
    needs_floor_decl: &mut bool,
    needs_div_guard: &mut bool,
) {
    match n {
        NumRegsRhs::Int {
            target,
            left,
            right,
            rhs_const,
        } => floor_div_op(
            target,
            left,
            right,
            code,
            needs_floor_decl,
            needs_div_guard,
            *rhs_const,
        ),
        NumRegsRhs::Float {
            target,
            left,
            right,
            rhs_const,
        } => floor_div_op(
            target,
            left,
            right,
            code,
            needs_floor_decl,
            needs_div_guard,
            *rhs_const,
        ),
    }
}

fn mod_regs(n: &NumRegsRhs, code: &mut String, needs_div_guard: &mut bool) {
    match n {
        NumRegsRhs::Int {
            target,
            left,
            right,
            rhs_const,
        } => mod_op(target, left, right, code, needs_div_guard, *rhs_const),
        NumRegsRhs::Float {
            target,
            left,
            right,
            rhs_const,
        } => mod_op(target, left, right, code, needs_div_guard, *rhs_const),
    }
}

fn neg_regs(u: &UnaryNum, code: &mut String) {
    match u {
        UnaryNum::Int { target, source } => neg_op(target, source, code),
        UnaryNum::Float { target, source } => neg_op(target, source, code),
    }
}

fn cmp_regs(
    c: &CmpRegs,
    int_cond: &str,
    flt_cond: &str,
    code: &mut String,
    needs_any_eq_decl: &mut bool,
) {
    match c {
        CmpRegs::Int {
            target,
            left,
            right,
        } => cmp_op(target, left, right, int_cond, flt_cond, code),
        CmpRegs::Float {
            target,
            left,
            right,
        } => cmp_op(target, left, right, int_cond, flt_cond, code),
        CmpRegs::Bool {
            target,
            left,
            right,
        } => cmp_op(target, left, right, int_cond, flt_cond, code),
        CmpRegs::Str {
            target,
            left,
            right,
        } => cmp_op(target, left, right, int_cond, flt_cond, code),
        CmpRegs::Ptr {
            target,
            left,
            right,
        } => cmp_op(target, left, right, int_cond, flt_cond, code),
        CmpRegs::Any {
            target,
            left,
            right,
        } => {
            *needs_any_eq_decl = true;
            code.push_str(&format!(
                "  %a{}.eq = call i32 @glm_any_eq(i128 %v{}, i128 %v{})\n\
                   %v{} = icmp ne i32 %a{}.eq, 0\n",
                target.id, left.id, right.id, target.id, target.id
            ));
        }
    }
}

fn emit_phi<R: Repr>(target: &Reg<R>, args: &[(BlockId, Reg<R>)], code: &mut String) {
    let pairs: Vec<String> = args
        .iter()
        .map(|(b, r)| format!("[ %v{}, %b{} ]", r.id, b))
        .collect();
    code.push_str(&format!(
        "  %v{} = phi {} {}\n",
        target.id,
        R::llvm(),
        pairs.join(", ")
    ));
}

#[allow(clippy::too_many_arguments)]
fn emit_table_get<E: Repr>(
    target: &Reg<E>,
    table: &Reg<Ptr>,
    index: &Reg<Int>,
    allocas: &mut String,
    code: &mut String,
    seam: usize,
    needs_tbl_get_decl: &mut bool,
    needs_tbl_get_any_decl: &mut bool,
) {
    if E::REG_FACE {
        *needs_tbl_get_any_decl = true;
        code.push_str(&format!(
            "  %v{target} = call i128 @glm_tbl_get_any(ptr %v{table}, i64 %v{index})\n",
            target = target.id,
            table = table.id,
            index = index.id
        ));
        return;
    }
    *needs_tbl_get_decl = true;
    let ety = E::storage();
    let f = seam;

    allocas.push_str(&format!("  %ts{f}.dst = alloca {ety}\n", f = f, ety = ety));

    code.push_str(&format!(
        "  call void @glm_tbl_get(ptr %v{table}, i64 %v{index}, ptr %ts{f}.dst, i64 {esize})\n",
        f = f,
        table = table.id,
        index = index.id,
        esize = E::esize()
    ));

    if E::IS_PACKED {
        code.push_str(&format!(
            "  %ts{f}.c = load i8, ptr %ts{f}.dst\n\
               %v{target} = icmp ne i8 %ts{f}.c, 0\n",
            f = f,
            target = target.id
        ));
    } else {
        code.push_str(&format!(
            "  %v{target} = load {ety}, ptr %ts{f}.dst\n",
            target = target.id,
            ety = ety,
            f = f
        ));
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_table_set_fast<E: Repr>(
    table: &Reg<Ptr>,
    index: &Reg<Int>,
    value: &Reg<E>,
    layout: &LayoutVerdict,
    cont: BlockId,
    allocas: &mut String,
    code: &mut String,
    seam: usize,
    needs_hdr_md: &mut bool,
    needs_tbl_set_decl: &mut bool,
    needs_tbl_set_any_decl: &mut bool,
) {
    *needs_hdr_md = true;
    let ety = E::storage();
    let f = seam;

    let cast_var = format!("%ts{}.c", f);

    let val_cast = if E::IS_PACKED {
        format!(
            "  {cv} = zext i1 %v{value} to i8\n",
            cv = cast_var,
            value = value.id
        )
    } else {
        String::new()
    };
    let val_use = if E::IS_PACKED {
        cast_var
    } else {
        format!("%v{value}", value = value.id)
    };

    if !E::REG_FACE {
        allocas.push_str(&format!("  %ts{f}.valp = alloca {ety}\n", f = f, ety = ety));
    }

    match layout {
        LayoutVerdict::Dense => {
            code.push_str(&format!(
                "{val_cast}\
                   %ts{f}.d = load ptr, ptr %v{table}, !alias.scope !0\n\
                   %ts{f}.s = getelementptr inbounds {ety}, ptr %ts{f}.d, i64 %v{index}\n\
                   store {ety} {val_use}, ptr %ts{f}.s, !noalias !0\n\
                   br label %b{cont}\n",
                val_cast = val_cast,
                f = f,
                table = table.id,
                index = index.id,
                ety = ety,
                val_use = val_use,
                cont = cont
            ));
        }
        LayoutVerdict::Sparse => {
            code.push_str(&format!(
                "{val_cast}\
                   {checked}\
                   br label %b{cont}\n",
                val_cast = val_cast,
                checked = checked_store::<E>(
                    f,
                    table,
                    index,
                    &val_use,
                    ety,
                    needs_tbl_set_decl,
                    needs_tbl_set_any_decl
                ),
                cont = cont
            ));
        }
        _ => {
            code.push_str(&format!(
                "{val_cast}\
                   %ts{f}.modep = getelementptr inbounds i8, ptr %v{table}, i64 32\n\
                   %ts{f}.mode = load i8, ptr %ts{f}.modep, !alias.scope !0\n\
                   %ts{f}.is_dense = icmp eq i8 %ts{f}.mode, 0\n\
                   br i1 %ts{f}.is_dense, label %bts{f}dense, label %bts{f}sparse\n\n\
                 bts{f}dense:\n\
                   %ts{f}.d = load ptr, ptr %v{table}, !alias.scope !0\n\
                   %ts{f}.s = getelementptr inbounds {ety}, ptr %ts{f}.d, i64 %v{index}\n\
                   store {ety} {val_use}, ptr %ts{f}.s, !noalias !0\n\
                   br label %b{cont}\n\n\
                 bts{f}sparse:\n\
                   {checked}\
                   br label %b{cont}\n",
                val_cast = val_cast,
                checked = checked_store::<E>(
                    f,
                    table,
                    index,
                    &val_use,
                    ety,
                    needs_tbl_set_decl,
                    needs_tbl_set_any_decl
                ),
                f = f,
                table = table.id,
                index = index.id,
                ety = ety,
                val_use = val_use,
                cont = cont
            ));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn checked_store<E: Repr>(
    f: usize,
    table: &Reg<Ptr>,
    index: &Reg<Int>,
    val_use: &str,
    ety: &str,
    needs_tbl_set_decl: &mut bool,
    needs_tbl_set_any_decl: &mut bool,
) -> String {
    if E::REG_FACE {
        *needs_tbl_set_any_decl = true;
        format!(
            "  call void @glm_tbl_set_any(ptr %v{table}, i64 %v{index}, i128 {v})\n",
            table = table.id,
            index = index.id,
            v = val_use
        )
    } else {
        *needs_tbl_set_decl = true;
        format!(
            "  store {ety} {v}, ptr %ts{f}.valp\n\
               call void @glm_tbl_set(ptr %v{table}, i64 %v{index}, ptr %ts{f}.valp)\n",
            ety = ety,
            v = val_use,
            f = f,
            table = table.id,
            index = index.id
        )
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_table_set<E: Repr>(
    table: &Reg<Ptr>,
    index: &Reg<Int>,
    value: &Reg<E>,
    allocas: &mut String,
    code: &mut String,
    seam: usize,
    needs_tbl_set_decl: &mut bool,
    needs_tbl_set_any_decl: &mut bool,
) {
    if E::REG_FACE {
        *needs_tbl_set_any_decl = true;
        code.push_str(&format!(
            "  call void @glm_tbl_set_any(ptr %v{table}, i64 %v{index}, i128 %v{value})\n",
            table = table.id,
            index = index.id,
            value = value.id
        ));
        return;
    }
    *needs_tbl_set_decl = true;
    let ety = E::storage();
    let f = seam;

    allocas.push_str(&format!("  %ts{f}.valp = alloca {ety}\n", f = f, ety = ety));

    if E::IS_PACKED {
        code.push_str(&format!(
            "  %ts{f}.z = zext i1 %v{value} to i8\n\
               store i8 %ts{f}.z, ptr %ts{f}.valp\n",
            f = f,
            value = value.id
        ));
    } else {
        code.push_str(&format!(
            "  store {ety} %v{value}, ptr %ts{f}.valp\n",
            ety = ety,
            value = value.id,
            f = f
        ));
    }
    code.push_str(&format!(
        "  call void @glm_tbl_set(ptr %v{table}, i64 %v{index}, ptr %ts{f}.valp)\n",
        table = table.id,
        index = index.id,
        f = f
    ));
}

fn math_op<N: Repr>(
    target: &Reg<N>,
    left: &Reg<N>,
    right: &Reg<N>,
    int_op: &str,
    flt_op: &str,
    code: &mut String,
) {
    if N::IS_FLOAT {
        code.push_str(&format!(
            "  %v{} = {} double %v{}, %v{}\n",
            target.id, flt_op, left.id, right.id
        ));
    } else {
        code.push_str(&format!(
            "  %v{} = {} i64 %v{}, %v{}\n",
            target.id, int_op, left.id, right.id
        ));
    }
}

fn neg_op<N: Repr>(target: &Reg<N>, source: &Reg<N>, code: &mut String) {
    if N::IS_FLOAT {
        code.push_str(&format!(
            "  %v{} = fsub double 0.0, %v{}\n",
            target.id, source.id
        ));
    } else {
        code.push_str(&format!("  %v{} = sub i64 0, %v{}\n", target.id, source.id));
    }
}

#[allow(clippy::too_many_arguments)]
fn floor_div_op<N: Repr>(
    target: &Reg<N>,
    left: &Reg<N>,
    right: &Reg<N>,
    code: &mut String,
    needs_floor_decl: &mut bool,
    needs_div_guard: &mut bool,
    rhs_const: Option<i64>,
) {
    if N::IS_FLOAT {
        *needs_floor_decl = true;
        code.push_str(&format!(
            "  %t{}.0 = fdiv double %v{}, %v{}\n",
            target.id, left.id, right.id
        ));
        code.push_str(&format!(
            "  %v{} = call double @llvm.floor.f64(double %t{}.0)\n",
            target.id, target.id
        ));
    } else {
        let divsr: String = match rhs_const {
            Some(k) if k != 0 => format!("%v{right}", right = right.id),
            _ => {
                *needs_div_guard = true;
                code.push_str(&format!(
                    "  call void @glm_div_zero_guard(i64 %v{})\n",
                    right.id
                ));
                code.push_str(&format!(
                    "  %t{}.g0 = icmp eq i64 %v{}, -1\n",
                    target.id, right.id
                ));
                code.push_str(&format!(
                    "  %t{}.g1 = select i1 %t{}.g0, i64 1, i64 %v{}\n",
                    target.id, target.id, right.id
                ));
                format!("%t{target}.g1", target = target.id)
            }
        };
        code.push_str(&format!(
            "  %t{}.0 = sdiv i64 %v{}, {}\n",
            target.id, left.id, divsr
        ));
        code.push_str(&format!(
            "  %t{}.1 = srem i64 %v{}, {}\n",
            target.id, left.id, divsr
        ));
        code.push_str(&format!(
            "  %t{}.2 = icmp ne i64 %t{}.1, 0\n",
            target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.3 = xor i64 %v{}, %v{}\n",
            target.id, left.id, right.id
        ));
        code.push_str(&format!(
            "  %t{}.4 = icmp slt i64 %t{}.3, 0\n",
            target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.5 = and i1 %t{}.2, %t{}.4\n",
            target.id, target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.6 = sub i64 %t{}.0, 1\n",
            target.id, target.id
        ));
        code.push_str(&format!(
            "  %v{} = select i1 %t{}.5, i64 %t{}.6, i64 %t{}.0\n",
            target.id, target.id, target.id, target.id
        ));
    }
}

fn mod_op<N: Repr>(
    target: &Reg<N>,
    left: &Reg<N>,
    right: &Reg<N>,
    code: &mut String,
    needs_div_guard: &mut bool,
    rhs_const: Option<i64>,
) {
    if N::IS_FLOAT {
        code.push_str(&format!(
            "  %t{}.0 = frem double %v{}, %v{}\n",
            target.id, left.id, right.id
        ));
        code.push_str(&format!(
            "  %t{}.1 = fcmp ogt double %t{}.0, 0.0\n",
            target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.2 = fcmp olt double %v{}, 0.0\n",
            target.id, right.id
        ));
        code.push_str(&format!(
            "  %t{}.3 = and i1 %t{}.1, %t{}.2\n",
            target.id, target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.4 = fcmp olt double %t{}.0, 0.0\n",
            target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.5 = fcmp ogt double %v{}, 0.0\n",
            target.id, right.id
        ));
        code.push_str(&format!(
            "  %t{}.6 = and i1 %t{}.4, %t{}.5\n",
            target.id, target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.7 = or i1 %t{}.3, %t{}.6\n",
            target.id, target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.8 = fadd double %t{}.0, %v{}\n",
            target.id, target.id, right.id
        ));
        code.push_str(&format!(
            "  %v{} = select i1 %t{}.7, double %t{}.8, double %t{}.0\n",
            target.id, target.id, target.id, target.id
        ));
    } else {
        let divsr: String = match rhs_const {
            Some(k) if k != 0 => format!("%v{right}", right = right.id),
            _ => {
                *needs_div_guard = true;
                code.push_str(&format!(
                    "  call void @glm_div_zero_guard(i64 %v{})\n",
                    right.id
                ));
                code.push_str(&format!(
                    "  %t{}.g0 = icmp eq i64 %v{}, -1\n",
                    target.id, right.id
                ));
                code.push_str(&format!(
                    "  %t{}.g1 = select i1 %t{}.g0, i64 1, i64 %v{}\n",
                    target.id, target.id, right.id
                ));
                format!("%t{target}.g1", target = target.id)
            }
        };
        code.push_str(&format!(
            "  %t{}.0 = srem i64 %v{}, {}\n",
            target.id, left.id, divsr
        ));
        code.push_str(&format!(
            "  %t{}.1 = icmp ne i64 %t{}.0, 0\n",
            target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.2 = xor i64 %t{}.0, %v{}\n",
            target.id, target.id, right.id
        ));
        code.push_str(&format!(
            "  %t{}.3 = icmp slt i64 %t{}.2, 0\n",
            target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.4 = and i1 %t{}.1, %t{}.3\n",
            target.id, target.id, target.id
        ));
        code.push_str(&format!(
            "  %t{}.5 = add i64 %t{}.0, %v{}\n",
            target.id, target.id, right.id
        ));
        code.push_str(&format!(
            "  %v{} = select i1 %t{}.4, i64 %t{}.5, i64 %t{}.0\n",
            target.id, target.id, target.id, target.id
        ));
    }
}

fn cmp_op<T: Repr>(
    target: &Reg<Bool>,
    left: &Reg<T>,
    right: &Reg<T>,
    int_cond: &str,
    flt_cond: &str,
    code: &mut String,
) {
    if T::IS_FLOAT {
        code.push_str(&format!(
            "  %v{} = fcmp {} double %v{}, %v{}\n",
            target.id, flt_cond, left.id, right.id
        ));
    } else {
        code.push_str(&format!(
            "  %v{} = icmp {} {} %v{}, %v{}\n",
            target.id,
            int_cond,
            T::llvm(),
            left.id,
            right.id
        ));
    }
}

#[cfg(test)]
mod label_closure_tests {
    use super::assert_labels_closed;

    #[test]
    fn closed_module_passes() {
        assert_labels_closed(
            "define ptr @f() {\n\
             entry:\n\
             \x20 br label %b0\n\
             \nb0:\n\
             \x20 %v1 = phi i64 [ 0, %entry ], [ 1, %b3 ]\n\
             \x20 br i1 %v2, label %bts0dense, label %bts0sparse\n\
             \nbts0dense:\n\
             \x20 store i64 1, ptr %p\n\
             \x20 br label %b3\n\
             \nbts0sparse:\n\
             \x20 call void @glm_tbl_set(ptr %t, i64 1, ptr %v)\n\
             \x20 br label %b3\n\
             \nb3:\n\
             \x20 br label %b0\n\
             }\n",
        );
    }

    #[test]
    fn string_pool_literals_cannot_false_positive() {
        assert_labels_closed(
            "@.str = constant [9 x i8] c\"label %x\\00\"\n\
             define ptr @f() {\n\
             entry:\n\
             \x20 ret ptr null\n\
             }\n",
        );
    }

    #[test]
    #[should_panic(expected = "names block 'b1'")]
    fn dangling_reference_panics() {
        assert_labels_closed(
            "define ptr @f() {\n\
             entry:\n\
             \x20 br label %b0\n\
             \nb0:\n\
             \x20 %v1 = phi i64 [ 0, %entry ], [ 1, %b1 ]\n\
             \x20 ret ptr null\n\
             }\n",
        );
    }
}

#[cfg(test)]
mod fast_store_tail_tests {
    use super::{assert_labels_closed, emit_table_set_fast};
    use crate::ir::{Int, Ptr, Reg};
    use crate::shape::LayoutVerdict;

    #[test]
    fn growing_diamond_closes_into_the_real_cont_block() {
        let table = Reg::<Ptr>::new(1);
        let index = Reg::<Int>::new(2);
        let value = Reg::<Int>::new(3);
        let mut allocas = String::new();
        let mut code = String::new();
        let mut hdr_md = false;
        let mut set_decl = false;
        let mut set_any_decl = false;
        emit_table_set_fast::<Int>(
            &table,
            &index,
            &value,
            &LayoutVerdict::Growing,
            5,
            &mut allocas,
            &mut code,
            7,
            &mut hdr_md,
            &mut set_decl,
            &mut set_any_decl,
        );
        assert_eq!(code.matches("br label %b5").count(), 2);
        assert!(!code.contains("cont:"));
        assert_labels_closed(&format!(
            "define ptr @f() {{\n\
             entry:\n\
             \x20 br label %b9\n\
             \nb9:\n{code}\
             b5:\n\
             \x20 ret ptr null\n\
             }}\n"
        ));
    }
}
