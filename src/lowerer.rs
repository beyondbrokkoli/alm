// AST -> SSA IR lowering. Every acceptance decision rides facts
// (ShapeFacts); this walk lowers and never re-derives.

mod bridges;

use crate::ast::{BinOp, CtorKey, Expr, NodeId, Stmt, UnOp};
use crate::diag::Diagnostic;
use crate::ir::{
    AnyReg, BasicBlock, BlockId, Bool, CellRepr, DbgBind, Instruction, Int, IrProgram, Ptr, Reg,
    RegId, RegKind, SourceLoc, TableKey, Terminator, repr_of,
};
use crate::shape::{
    ArmFreeEntry, DoExitFree, FfiVerb, Keep, KeyLane, LayoutVerdict, ShapeFacts, TagSrc, Ty,
};
use alm_rt::{signal, trace};
use bridges::{
    NumPair, NumSingle, OrdPair, any_of, bool_of, int_of, num_pair, num_single, ord_pair, phi_of,
    phi_push, pooled_ptr_of, ptr_of, str_lane, string_repr,
};
use std::collections::{BTreeMap, BTreeSet};

/// A lowering rejection — a typed `Diagnostic` (H11); desync-ness is
/// the `Desync` variant on the payload, matched by kind.
pub struct LowerError(pub Diagnostic);

impl LowerError {
    pub fn is_desync(&self) -> bool {
        self.0.is_desync()
    }
}

pub fn boundary_elem_of(elem: Ty) -> alm_rt::AlmElem {
    match elem {
        Ty::Flt => alm_rt::AlmElem::Float,
        Ty::Bool => alm_rt::AlmElem::Boolean,
        Ty::Str => alm_rt::AlmElem::String,
        Ty::Any => alm_rt::AlmElem::Any,
        Ty::Int | Ty::Tbl(_) | Ty::Unknown(_) => alm_rt::AlmElem::Integer,
        Ty::Ffi | Ty::FfiLib | Ty::Coro => alm_rt::AlmElem::Integer,
        // a closure never rides the boundary (W3-R5's reject pin) —
        // the boundary elem fact is scalar-only by construction
        Ty::Closure(_) => unreachable!("a closure never rides the boundary elem"),
        // the boundary elem fact is a resolved checker value — flow
        // state never rides the artifact path
        Ty::Pending | Ty::Conflict => unreachable!("flow state never rides the artifact path"),
    }
}

fn join_phi_ty(a: &Ty, b: &Ty) -> Ty {
    if a == b {
        return a.clone();
    }
    let heap = |t: &Ty| matches!(t, Ty::Tbl(_));
    if heap(a) { a.clone() } else { b.clone() }
}

enum ReturnKind {
    Boundary,
    Inline { ty: Ty },
}

struct ReturnCtx {
    kind: ReturnKind,
    exit: Option<BlockId>,
    args: Vec<(BlockId, AnyReg)>,
}

#[derive(Clone)]
struct Local {
    reg: AnyReg,
    ty: Ty,
    layout: LayoutVerdict,
}

#[derive(Clone)]
struct TypedReg {
    reg: AnyReg,
    ty: Ty,
}

struct LoopCtx {
    guard_reg: RegId,
    reserved: Vec<RegId>,
    nested_fills: Vec<(String, Reg<Int>)>,
}

/// One per ACTIVE loop (pushed for every While, not just fill-converted
/// ones): breaks record (block, snapshot of phi_order locals) and the exit
/// block gains one phi per loop-carried var ONLY when breaks exist — so
/// break-free while loops lower bit-for-bit as before.
struct BreakCtx {
    exit_block: BlockId,
    phi_vars: Vec<String>,
    breaks: Vec<(BlockId, Vec<Local>)>,
}

struct FreeHandles {
    site_regs: BTreeMap<usize, (Reg<Ptr>, u32)>,
}

struct FillCtxs {
    loop_ctxs: Vec<LoopCtx>,
}

pub struct IrLowerer<'a> {
    pub blocks: Vec<BasicBlock>,
    pub diagnostics: Vec<Diagnostic>,
    current_block: BlockId,
    free_reg: RegId,
    scopes: Vec<BTreeMap<String, Local>>,
    fills: FillCtxs,
    handles: FreeHandles,
    shape: &'a ShapeFacts,
    cur_loc: Option<SourceLoc>,
    ghost_keeps: BTreeMap<usize, Reg<Ptr>>,
    if_tag_regs: BTreeMap<NodeId, Reg<Bool>>,
    call_tag_regs: BTreeMap<NodeId, Reg<Bool>>,

    ctrl_depth: u32,
    return_ctxs: Vec<ReturnCtx>,
    break_ctxs: Vec<BreakCtx>,
    inline_stack: Vec<NodeId>,
    /// the OUTERMOST call expr of every inline expansion currently being
    /// lowered (bottom = outermost site) — the lowerer's derivation of
    /// the `(call expr, expansion site)` fact keys it shares with the
    /// checker. Derived from this stack alone: both halves walk the
    /// identical AST in the identical order, so the sites agree without
    /// any shared counter.
    expansion_sites: Vec<NodeId>,
    /// the break-ctx depth each expansion began at — defense in depth:
    /// a break inside an expansion may only bind a loop of its OWN
    /// body, never the caller's (whose ctx would sit below the base).
    expansion_break_bases: Vec<usize>,
    /// W3a: the per-statement env mint memo — every closure created by
    /// ONE statement shares ONE env (sibling sharing, L3); the memo
    /// resets at each statement lowering. `stored` guards the union:
    /// a later creation in the same statement only stores its
    /// not-yet-stored captures.
    env_memo: Option<EnvMemo>,
    /// W3a: every minted env — freed at ROOT exit (W3-R1: module
    /// lifetime; the deep free reclaims boxes and moved tables).
    env_regs: Vec<Reg<Ptr>>,
    /// W3a: per ACTIVE call-through expansion — the env register and
    /// the face (capture name → cell type). Captures materialize as
    /// ordinary vars at entry; scalar rebinds write the box back.
    env_ctxs: Vec<EnvCtx>,
    /// the statement currently lowering (the env memo's key).
    cur_stmt: Option<NodeId>,
}

/// W3a's env representation: a strkey table whose EVERY cell is a
/// table pointer — captured tables ride their own headers, captured
/// scalars ride one-cell dense boxes of their own elem (the runtime's
/// deep free chases only pointer cells, so a mixed env must keep
/// every cell pointer-shaped; boxes carry contains_tables=0 and are
/// freed as headers, their scalar payloads never chased).
struct EnvMemo {
    stmt: NodeId,
    reg: Reg<Ptr>,
    stored: BTreeSet<String>,
}

struct EnvCtx {
    reg: Reg<Ptr>,
    faces: BTreeMap<String, Ty>,
}
impl Clone for EnvCtx {
    fn clone(&self) -> Self {
        EnvCtx {
            reg: self.reg,
            faces: self.faces.clone(),
        }
    }
}

impl<'a> IrLowerer<'a> {
    pub fn new(shape: &'a ShapeFacts) -> Self {
        Self {
            blocks: vec![BasicBlock::new(0)],
            diagnostics: Vec::new(),
            current_block: 0,
            free_reg: 0,
            scopes: vec![BTreeMap::new()],
            fills: FillCtxs {
                loop_ctxs: Vec::new(),
            },
            shape,
            cur_loc: None,
            handles: FreeHandles {
                site_regs: BTreeMap::new(),
            },
            ghost_keeps: BTreeMap::new(),
            if_tag_regs: BTreeMap::new(),
            call_tag_regs: BTreeMap::new(),
            ctrl_depth: 0,
            return_ctxs: Vec::new(),
            break_ctxs: Vec::new(),
            inline_stack: Vec::new(),
            expansion_sites: Vec::new(),
            expansion_break_bases: Vec::new(),
            env_memo: None,
            env_regs: Vec::new(),
            env_ctxs: Vec::new(),
            cur_stmt: None,
        }
    }

    fn new_block(&mut self) -> BlockId {
        let id = self.blocks.len();
        self.blocks.push(BasicBlock::new(id));
        id
    }

    fn next_reg(&mut self) -> RegId {
        let r = self.free_reg;
        self.free_reg += 1;
        r
    }

    fn emit(&mut self, instr: Instruction) {
        let block = &mut self.blocks[self.current_block];
        block.locs.push(self.cur_loc);
        block.instrs.push(instr);
    }

    fn terminate(&mut self, term: Terminator) {
        let block = &mut self.blocks[self.current_block];
        block.term_loc = self.cur_loc;
        block.terminator = Some(term);
    }

    fn push_dbg_bind(&mut self, name: &str, reg: AnyReg, param: Option<u32>) {
        let after = self.blocks[self.current_block].instrs.len().checked_sub(1);
        if let Some(after) = after {
            self.blocks[self.current_block].dbg_values.push(DbgBind {
                after,
                name: name.to_string(),
                reg: reg.id(),
                kind: reg.kind(),
                loc: self.cur_loc,
                param,
            });
        }
    }

    fn in_block<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push(BTreeMap::new());
        self.ctrl_depth += 1;
        let r = f(self);
        self.ctrl_depth -= 1;
        self.scopes.pop();
        r
    }

    fn at_depth<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.ctrl_depth += 1;
        let r = f(self);
        self.ctrl_depth -= 1;
        r
    }

    fn in_do<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push(BTreeMap::new());
        let r = f(self);
        self.scopes.pop();
        r
    }

    fn emit_scope_frees(&mut self, key: (NodeId, u8)) -> Result<(), LowerError> {
        let frees = self
            .shape
            .do_exit_frees
            .get(&key)
            .cloned()
            .unwrap_or_default();
        self.emit_frees(&frees)?;
        if let Some(arms) = self.shape.arm_do_exit_frees.get(&key) {
            for e in arms {
                self.emit_arm_free(e)?;
            }
        }
        Ok(())
    }

    fn resolve_keeps(&self, keeps: &[Keep]) -> Result<Vec<Reg<Ptr>>, LowerError> {
        let mut regs = Vec::new();
        for k in keeps {
            match k {
                Keep::Name(n) => {
                    let local = self.read_var(n)?;
                    let reg = ptr_of(local.reg).map_err(|_| {
                        LowerError(Diagnostic::desync(format!(
                            "Lower Error: borrower '{n}' planned as a keep holds a \
                             non-pointer register — the analyzer and the lowerer disagree"
                        )))
                    })?;
                    regs.push(reg);
                }
                Keep::Ghost(g) => {
                    let &r = self.ghost_keeps.get(g).ok_or_else(|| {
                        LowerError(Diagnostic::desync(
                            "Lower Error: a housed row's keep register was never \
                             captured — the analyzer and the lowerer disagree",
                        ))
                    })?;
                    regs.push(r);
                }
            }
        }
        regs.sort_unstable_by_key(|r| r.id);
        regs.dedup_by_key(|r| r.id);
        Ok(regs)
    }

    fn emit_arm_free(&mut self, e: &ArmFreeEntry) -> Result<(), LowerError> {
        let tag = match e.tag {
            TagSrc::If(stmt) => self.if_tag_regs.get(&stmt).copied(),
            TagSrc::Call(expr) => self.call_tag_regs.get(&expr).copied(),
        }
        .ok_or_else(|| {
            LowerError(Diagnostic::desync(
                "Lower Error: a mixed join's tag phi never lowered — \
                 the analyzer and the lowerer disagree",
            ))
        })?;
        let carrier = self.read_var(&e.carrier)?;
        let table = ptr_of(carrier.reg)?;
        let keep_regs = self.resolve_keeps(&e.keeps)?;
        if keep_regs.iter().any(|k| k.id == table.id) {
            return Ok(());
        }
        let c_reg = self.next_reg();
        self.emit(Instruction::LoadBool {
            target: Reg::new(c_reg),
            val: e.nothing_on,
        });
        let eq_reg = self.next_reg();
        self.cmp3(Instruction::Eq, eq_reg, tag, Reg::new(c_reg));
        let nothing_block = self.new_block();
        let free_block = self.new_block();
        let cont = self.new_block();
        self.terminate(Terminator::Branch {
            cond: Reg::new(eq_reg),
            true_block: nothing_block,
            false_block: free_block,
        });
        self.current_block = free_block;
        signal!(trace::TRACE_JOIN_ARM_FREE);
        if keep_regs.is_empty() {
            self.emit(Instruction::TableFree { table });
        } else {
            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
            self.emit(Instruction::TableFreeExcept {
                table,
                keeps: keep_regs,
            });
        }
        self.terminate(Terminator::Jump(cont));
        self.current_block = nothing_block;
        self.terminate(Terminator::Jump(cont));
        self.current_block = cont;
        Ok(())
    }

    fn emit_frees(&mut self, frees: &[DoExitFree]) -> Result<(), LowerError> {
        let mut plain: Vec<Reg<Ptr>> = Vec::new();
        let mut kept: Vec<(Reg<Ptr>, Vec<Reg<Ptr>>)> = Vec::new();
        for f in frees {
            let carrier = self.read_var(&f.carrier)?;
            // W3a's Extraction Law, lowering half: a closure-typed
            // register is a VIEW of its env — the mint is the one
            // owner, freed at root exit. A closure carrier here means
            // a face read reached a binding past the checker's
            // reject; freeing the view would fire an untracked second
            // free on a live env.
            if matches!(carrier.ty, Ty::Closure(_)) {
                return Err(LowerError(Diagnostic::desync(format!(
                    "a closure value's env has one owner (its mint) — '{}' carries a \
                     face; the checker and the lowerer disagree",
                    f.carrier
                ))));
            }
            let table = ptr_of(carrier.reg)?;
            signal!(trace::TRACE_DO_EXIT_FREE_PHI);
            if f.keeps.is_empty() {
                plain.push(table);
            } else {
                kept.push((table, self.resolve_keeps(&f.keeps)?));
            }
        }

        plain.sort_unstable_by_key(|reg| reg.id);
        plain.dedup_by_key(|reg| reg.id);
        let mut seen: BTreeSet<RegId> = BTreeSet::new();
        for (table, keeps) in kept {
            if keeps.iter().any(|k| k.id == table.id) || !seen.insert(table.id) {
                continue;
            }
            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
            self.emit(Instruction::TableFreeExcept { table, keeps });
        }
        for reg in plain.into_iter().rev() {
            if !seen.insert(reg.id) {
                continue;
            }
            self.emit(Instruction::TableFree { table: reg });
        }
        Ok(())
    }

    fn emit_root_frees(&mut self) -> Result<(), LowerError> {
        // W3a (the pin-owed register, census §3 cluster B row 17): an
        // env is never one of their keeps — the analyzer's keep
        // computation has no env concept, so nothing structural
        // verifies it; a keep naming an env register would exempt it
        // from the deep free it still needs (a leak). The census fires
        // in debug/test builds at the one site where envs and keeps
        // meet: the root tail, after every mint, before the env frees.
        for f in &self.shape.root_exit_frees {
            for k in &f.keeps {
                if let Keep::Name(n) = k {
                    let local = self.read_var(n)?;
                    let reg = ptr_of(local.reg).map_err(|_| {
                        LowerError(Diagnostic::desync(format!(
                            "Lower Error: borrower '{n}' planned as a keep holds a \
                             non-pointer register — the analyzer and the lowerer disagree"
                        )))
                    })?;
                    debug_assert!(
                        !self.env_regs.iter().any(|e| e.id == reg.id),
                        "an env register rode a root free's keeps — the env's one \
                         owner is its mint"
                    );
                }
            }
        }
        self.emit_frees(&self.shape.root_exit_frees)?;
        let arms = self.shape.arm_root_exit_frees.clone();
        for e in &arms {
            self.emit_arm_free(e)?;
        }
        // W3a, W3-R1: envs live to root exit. The deep free reclaims
        // the whole tree — boxes and moved-in tables alike — after the
        // name-carried frees (an env is never one of their keeps).
        let envs = std::mem::take(&mut self.env_regs);
        for env in envs {
            self.emit(Instruction::TableFree { table: env });
        }
        Ok(())
    }

    fn emit_stmt_temp_frees(&mut self, stmt: &Stmt) {
        let Some(sites) = self.shape.stmt_temp_frees.get(&stmt.id()) else {
            return;
        };
        self.emit_site_frees(sites, trace::TRACE_STMT_TEMP_FREE);
    }

    fn emit_cond_temp_frees(&mut self, stmt: &Stmt) {
        let Some(sites) = self.shape.cond_temp_frees.get(&stmt.id()) else {
            return;
        };
        self.emit_site_frees(sites, trace::TRACE_COND_TEMP_FREE);
    }

    fn emit_arm_temp_frees(&mut self, operand: &Expr) {
        let Some(sites) = self.shape.arm_temp_frees.get(&operand.id()) else {
            return;
        };
        self.emit_site_frees(sites, trace::TRACE_ARM_TEMP_FREE);
    }

    fn emit_site_frees(&mut self, sites: &[usize], slot: u8) {
        let mut free_regs: Vec<Reg<Ptr>> = sites
            .iter()
            .filter_map(|site| self.handles.site_regs.get(site).map(|(reg, _)| *reg))
            .collect();
        free_regs.sort_unstable_by_key(|reg| reg.id);
        free_regs.dedup_by_key(|reg| reg.id);
        for reg in free_regs.into_iter().rev() {
            signal!(slot);
            self.emit(Instruction::TableFree { table: reg });
        }
    }

    // The String repr invariant lives HERE, at the two binding choke
    // points: a value whose static type is String always enters (and
    // therefore leaves) the variable table tagged Str, whatever physical
    // path produced the register (cell reads, phis, nulls all emit the
    // pointer kind). Consumers can rely on it; producers need no
    // per-site normalization.
    fn declare_var(&mut self, name: String, reg: AnyReg, ty: Ty, layout: LayoutVerdict) {
        let reg = string_repr(&ty, reg);
        self.push_dbg_bind(&name, reg, None);
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name, Local { reg, ty, layout });
    }

    fn update_var(
        &mut self,
        name: &str,
        reg: AnyReg,
        ty: Ty,
        layout: LayoutVerdict,
    ) -> Result<(), LowerError> {
        let reg = string_repr(&ty, reg);
        for scope in self.scopes.iter_mut().rev() {
            if let Some(local) = scope.get_mut(name) {
                local.reg = reg;
                local.ty = ty;
                local.layout = layout;
                self.push_dbg_bind(name, reg, None);
                return Ok(());
            }
        }
        Err(LowerError(Diagnostic::lower("Undeclared variable")))
    }

    fn read_var(&self, name: &str) -> Result<Local, LowerError> {
        for scope in self.scopes.iter().rev() {
            if let Some(local) = scope.get(name) {
                return Ok(local.clone());
            }
        }
        Err(LowerError(Diagnostic::lower("Undeclared variable")))
    }

    fn has_var(&self, name: &str) -> bool {
        for scope in self.scopes.iter().rev() {
            if scope.contains_key(name) {
                return true;
            }
        }
        false
    }

    fn holds_value(&self, name: &str) -> bool {
        self.read_var(name)
            .is_ok_and(|local| !matches!(local.ty, Ty::Unknown(_)))
    }

    fn null_moved(&mut self, src: &str) -> Result<(), LowerError> {
        let local = self.read_var(src)?;
        let null_reg = self.next_reg();
        self.emit(Instruction::LoadNull {
            target: Reg::new(null_reg),
        });
        self.update_var(
            src,
            AnyReg::Ptr(Reg::new(null_reg)),
            local.ty.clone(),
            local.layout,
        )
    }

    fn null_moves_of(&mut self, stmt: &Stmt) -> Result<(), LowerError> {
        if let Some(srcs) = self.shape.move_poisons.get(&stmt.id()) {
            for src in srcs.clone() {
                self.null_moved(&src)?;
            }
        }
        Ok(())
    }

    pub fn lower_program(&mut self, stmts: &[Stmt]) -> IrProgram {
        let args_reg = self.next_reg();
        self.emit(Instruction::BindArgs {
            target: Reg::new(args_reg),
        });
        self.push_dbg_bind("arg", AnyReg::Ptr(Reg::new(args_reg)), Some(1));
        self.scopes[0].insert(
            "arg".to_string(),
            Local {
                reg: AnyReg::Ptr(Reg::new(args_reg)),
                ty: Ty::Tbl(Box::new(
                    self.shape.boundary_elem.clone().unwrap_or(Ty::Unknown(0)),
                )),
                layout: LayoutVerdict::default(),
            },
        );
        self.return_ctxs.push(ReturnCtx {
            kind: ReturnKind::Boundary,
            exit: None,
            args: Vec::new(),
        });
        for stmt in stmts {
            match self.lower_stmt(stmt) {
                Ok(_) => {}
                Err(e) => {
                    let desync = e.is_desync();
                    // the site-stamp: the stmt's own line off its own
                    // loc (H6: no map — the stamp rides the node)
                    self.diagnostics
                        .push(e.0.with_site(Some(stmt.loc().line as usize)));
                    signal!(trace::TRACE_GHOST_BAIL_LOWERER);
                    if desync {
                        signal!(trace::TRACE_ENG_DESYNC);
                    }
                    break;
                }
            }
        }
        if let Err(e) = self.emit_root_frees() {
            let desync = e.is_desync();
            self.diagnostics.push(e.0);
            signal!(trace::TRACE_GHOST_BAIL_LOWERER);
            if desync {
                signal!(trace::TRACE_ENG_DESYNC);
            }
        }
        if let Err(e) = self.finalize_return_ctx() {
            let desync = e.is_desync();
            self.diagnostics.push(e.0);
            signal!(trace::TRACE_GHOST_BAIL_LOWERER);
            if desync {
                signal!(trace::TRACE_ENG_DESYNC);
            }
        }
        IrProgram {
            blocks: std::mem::take(&mut self.blocks),
            boundary_elem: self.shape.boundary_elem.clone().map(boundary_elem_of),
            entry: crate::ir::EntryKind::Lib,
            source_file: std::path::PathBuf::new(),
        }
    }

    fn zero_reg(&mut self, kind: RegKind) -> AnyReg {
        let r = self.next_reg();
        match kind {
            RegKind::Int => {
                self.emit(Instruction::LoadInt {
                    target: Reg::new(r),
                    val: 0,
                });
                AnyReg::Int(Reg::new(r))
            }
            RegKind::Float => {
                self.emit(Instruction::LoadFloat {
                    target: Reg::new(r),
                    val: 0.0,
                });
                AnyReg::Float(Reg::new(r))
            }
            RegKind::Bool => {
                self.emit(Instruction::LoadBool {
                    target: Reg::new(r),
                    val: false,
                });
                AnyReg::Bool(Reg::new(r))
            }
            RegKind::Ptr => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(r),
                });
                AnyReg::Ptr(Reg::new(r))
            }
            RegKind::Any => {
                self.emit(Instruction::LoadAnyZero {
                    target: Reg::new(r),
                });
                AnyReg::Any(Reg::new(r))
            }
        }
    }

    fn finalize_return_ctx(&mut self) -> Result<Option<AnyReg>, LowerError> {
        let ctx = self
            .return_ctxs
            .pop()
            .expect("lower_program pushes the root return context");
        let Some(exit) = ctx.exit else {
            if matches!(ctx.kind, ReturnKind::Boundary)
                && self.blocks[self.current_block].terminator.is_none()
            {
                self.terminate(Terminator::Halt);
            }
            let kind = match &ctx.kind {
                ReturnKind::Boundary => RegKind::Ptr,
                ReturnKind::Inline { ty } => repr_of(ty),
            };
            return match ctx.kind {
                ReturnKind::Boundary => Ok(None),
                ReturnKind::Inline { ty } => Ok(Some(string_repr(&ty, self.zero_reg(kind)))),
            };
        };
        let (kind, boundary, ret_ty) = match &ctx.kind {
            ReturnKind::Boundary => (RegKind::Ptr, true, None),
            ReturnKind::Inline { ty } => (repr_of(ty), false, Some(ty)),
        };
        let mut args = ctx.args;
        if self.blocks[self.current_block].terminator.is_none() {
            let fallthrough = if boundary {
                let r = self.next_reg();
                self.emit(Instruction::LoadNull {
                    target: Reg::new(r),
                });
                AnyReg::Ptr(Reg::new(r))
            } else {
                match ret_ty {
                    Some(ty) => string_repr(ty, self.zero_reg(kind)),
                    None => self.zero_reg(kind),
                }
            };
            self.terminate(Terminator::Jump(exit));
            args.push((self.current_block, fallthrough));
        }
        let phi_reg = self.next_reg();
        let phi = phi_of(kind, phi_reg, args)?;
        self.current_block = exit;
        self.emit(Instruction::Phi(phi));
        if boundary {
            self.terminate(Terminator::Return(Reg::new(phi_reg)));
            return Ok(None);
        }
        Ok(Some(match ret_ty {
            Some(ty) => string_repr(ty, kind.reg(phi_reg)),
            None => kind.reg(phi_reg),
        }))
    }

    /// The per-instantiation half of the access/key fact keys, derived
    /// exactly as the checker derives them (`fact_site` there): the
    /// OUTERMOST expansion the current expression is being lowered
    /// inside — the expression itself at no expansion.
    fn fact_site(&self, expr: NodeId) -> NodeId {
        self.expansion_sites.first().copied().unwrap_or(expr)
    }

    /// Table keys: a String literal folds to its negative interned
    /// identity at COMPILE time (StrKeyConst — the whole point of
    /// hash-derived keys: zero runtime work for `t.x` / `t["x"]` /
    /// record fields); a String-typed dynamic key (`t[s]`) lowers to
    /// alm_str_key (StrKey — one prefix load off the pooled handle);
    /// anything else is the existing Integer lane. The returned
    /// TableKey keeps the two lanes apart at the type level: only the
    /// two derivations can construct the Str lane, so no user integer
    /// can address a record cell. WHICH lane a dynamic key rides is
    /// the checker's recorded decision (`index_key_lanes`, signal 178)
    /// — this walk consumes it, never re-derives it.
    fn lower_index_key(&mut self, key: &Expr) -> Result<TableKey, LowerError> {
        if let Expr::String { value: s, .. } = key {
            let r = self.next_reg();
            self.emit(Instruction::StrKeyConst {
                target: Reg::new(r),
                val: alm_rt::rt::str_key_of_bytes(s.as_bytes()),
            });
            return Ok(TableKey::Str(Reg::new(r)));
        }
        let lane = *self
            .shape
            .index_key_lanes
            .get(&(key.id(), self.fact_site(key.id())))
            .ok_or_else(|| {
                LowerError(Diagnostic::desync(
                    "Lower Error: an index key carries no recorded lane — \
                     the checker and the lowerer disagree",
                ))
            })?;
        let TypedReg { reg, .. } = self.lower_expr(key, None)?;
        match lane {
            KeyLane::Str => {
                // a String read out of a cell (or joined at a phi) carries
                // the pointer face; the two are the same pooled handle
                let s = str_lane(reg)?;
                let r = self.next_reg();
                self.emit(Instruction::StrKey {
                    target: Reg::new(r),
                    s,
                });
                signal!(trace::TRACE_LOWER_KEY_LANE);
                Ok(TableKey::Str(Reg::new(r)))
            }
            KeyLane::Int => {
                signal!(trace::TRACE_LOWER_KEY_LANE);
                Ok(TableKey::Int(int_of(reg)?))
            }
        }
    }

    /// The elem face of one access base, consumed straight from the
    /// checker's recorded decision (signal 180's fact) — the lowerer
    /// never re-derives the elem from its own type walk: one view of
    /// one cell kind everywhere, including adoption-bridged names.
    fn elem_face_of(&self, obj: &Expr) -> Result<Ty, LowerError> {
        let elem = self
            .shape
            .access_elems
            .get(&(obj.id(), self.fact_site(obj.id())))
            .cloned()
            .ok_or_else(|| {
                LowerError(Diagnostic::desync(
                    "Lower Error: a table access carries no recorded elem face — \
                     the checker and the lowerer disagree",
                ))
            })?;
        signal!(trace::TRACE_LOWER_ELEM_FACE);
        Ok(elem)
    }

    fn lower_stmt(&mut self, stmt: &Stmt) -> Result<(), LowerError> {
        self.cur_loc = Some(SourceLoc {
            line: stmt.loc().line,
            col: stmt.loc().col,
        });
        // W3a: one env per creation statement (sibling sharing) — the
        // memo resets at every statement lowering
        self.env_memo = None;
        self.cur_stmt = Some(stmt.id());
        match stmt {
            Stmt::LocalDecl { names, exprs, .. } => {
                let mut bindings = Vec::with_capacity(exprs.len());
                for expr in exprs {
                    let target_reg = self.next_reg();
                    let TypedReg { reg, ty } = self.lower_expr(expr, Some(target_reg))?;
                    let layout = self.lookup_layout_for(expr)?;
                    bindings.push((reg, ty, layout));
                }
                while bindings.len() < names.len() {
                    let name = &names[bindings.len()];
                    let ty = self
                        .shape
                        .local_types
                        .get(&(
                            stmt.id(),
                            self.expansion_sites.first().copied(),
                            name.clone(),
                        ))
                        .cloned()
                        .ok_or_else(|| {
                            LowerError(Diagnostic::desync(
                                "Lower Error: a bare declaration carries no resolved type — \
                                 the checker and the lowerer disagree",
                            ))
                        })?;
                    let reg_id = self.next_reg();
                    let reg = match &ty {
                        Ty::Int => {
                            self.emit(Instruction::LoadInt {
                                target: Reg::new(reg_id),
                                val: 0,
                            });
                            AnyReg::Int(Reg::new(reg_id))
                        }
                        Ty::Flt => {
                            self.emit(Instruction::LoadFloat {
                                target: Reg::new(reg_id),
                                val: 0.0,
                            });
                            AnyReg::Float(Reg::new(reg_id))
                        }
                        Ty::Bool => {
                            self.emit(Instruction::LoadBool {
                                target: Reg::new(reg_id),
                                val: false,
                            });
                            AnyReg::Bool(Reg::new(reg_id))
                        }
                        Ty::Tbl(_) | Ty::Unknown(_) | Ty::Str | Ty::Closure(_) => {
                            self.emit(Instruction::LoadNull {
                                target: Reg::new(reg_id),
                            });
                            AnyReg::Ptr(Reg::new(reg_id))
                        }
                        Ty::Ffi | Ty::FfiLib | Ty::Coro => {
                            self.emit(Instruction::LoadNull {
                                target: Reg::new(reg_id),
                            });
                            AnyReg::Ptr(Reg::new(reg_id))
                        }
                        Ty::Any => {
                            self.emit(Instruction::LoadAnyZero {
                                target: Reg::new(reg_id),
                            });
                            AnyReg::Any(Reg::new(reg_id))
                        }
                        // local_types is a resolved constraint-store value —
                        // flow state never rides the artifact path
                        Ty::Pending | Ty::Conflict => {
                            unreachable!("flow state never rides the artifact path")
                        }
                    };
                    bindings.push((reg, ty, LayoutVerdict::default()));
                }
                if let Some(names) = self.shape.rebind_frees.get(&stmt.id()) {
                    for (n, keeps) in names {
                        let displaced = self.read_var(n)?;
                        let table = ptr_of(displaced.reg)?;
                        let keep_regs = self.resolve_keeps(keeps)?;
                        if keep_regs.iter().any(|k| k.id == table.id) {
                            continue;
                        }
                        if keep_regs.is_empty() {
                            self.emit(Instruction::TableFree { table });
                        } else {
                            signal!(trace::TRACE_REBIND_FREE);
                            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
                            self.emit(Instruction::TableFreeExcept {
                                table,
                                keeps: keep_regs,
                            });
                        }
                        signal!(trace::TRACE_REBIND_FREE);
                    }
                }
                if let Some(arms) = self.shape.arm_rebind_frees.get(&stmt.id()) {
                    for e in arms {
                        self.emit_arm_free(e)?;
                    }
                }
                for (name, (reg, ty, layout)) in names.iter().zip(bindings) {
                    self.declare_var(name.clone(), reg, ty, layout);
                }
                self.null_moves_of(stmt)?;
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::Assignment { name, expr, .. } => {
                // the sugar's #define face (D4): a fn-literal assignment
                // to a name the lowering tables do not hold DECLARES it —
                // the same placeholder slot `local f = function` gets
                // (expansions resolve through the call-site facts, the
                // name slot never carries a value)
                if matches!(expr, Expr::Function { .. }) && !self.has_var(name) {
                    let target_reg = self.next_reg();
                    let TypedReg { reg, ty } = self.lower_expr(expr, Some(target_reg))?;
                    let layout = self.lookup_layout_for(expr)?;
                    self.declare_var(name.clone(), reg, ty, layout);
                    return Ok(());
                }
                if matches!(expr, Expr::Nil { .. }) {
                    let local = self.read_var(name)?;
                    if self.shape.is_free(stmt) {
                        let table = ptr_of(local.reg)?;
                        let keep_regs = self
                            .shape
                            .free_keeps
                            .get(&stmt.id())
                            .map(|ks| self.resolve_keeps(ks))
                            .transpose()?
                            .unwrap_or_default();
                        if keep_regs.iter().any(|k| k.id == table.id) {
                        } else if keep_regs.is_empty() {
                            self.emit(Instruction::TableFree { table });
                        } else {
                            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
                            self.emit(Instruction::TableFreeExcept {
                                table,
                                keeps: keep_regs,
                            });
                        }
                    }
                    if let Some(arms) = self.shape.arm_free_sites.get(&stmt.id()) {
                        for e in arms {
                            self.emit_arm_free(e)?;
                        }
                    }
                    let null_reg = self.next_reg();
                    self.emit(Instruction::LoadNull {
                        target: Reg::new(null_reg),
                    });
                    self.update_var(
                        name,
                        AnyReg::Ptr(Reg::new(null_reg)),
                        local.ty.clone(),
                        local.layout,
                    )?;
                    return Ok(());
                }
                let new_reg = self.next_reg();
                let TypedReg {
                    reg: actual_reg,
                    ty,
                } = self.lower_expr(expr, Some(new_reg))?;
                let layout = self.lookup_layout_for(expr)?;
                if let Some(names) = self.shape.rebind_frees.get(&stmt.id()) {
                    for (n, keeps) in names {
                        let displaced = self.read_var(n)?;
                        let table = ptr_of(displaced.reg)?;
                        let keep_regs = self.resolve_keeps(keeps)?;
                        if keep_regs.iter().any(|k| k.id == table.id) {
                            continue;
                        }
                        if keep_regs.is_empty() {
                            self.emit(Instruction::TableFree { table });
                        } else {
                            signal!(trace::TRACE_REBIND_FREE);
                            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
                            self.emit(Instruction::TableFreeExcept {
                                table,
                                keeps: keep_regs,
                            });
                        }
                        signal!(trace::TRACE_REBIND_FREE);
                    }
                }
                if let Some(arms) = self.shape.arm_rebind_frees.get(&stmt.id()) {
                    for e in arms {
                        self.emit_arm_free(e)?;
                    }
                }
                self.update_var(name, actual_reg, ty, layout)?;
                // W3a: a captured scalar's rebind writes the env box —
                // later calls (and siblings) read it back (L3)
                self.env_write_back(name, actual_reg)?;
                self.null_moves_of(stmt)?;
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::IndexAssign {
                obj, key, value, ..
            } => {
                let TypedReg { reg: t_any, .. } = self.lower_expr(obj, None)?;
                let t_reg = ptr_of(t_any)?;
                let key = self.lower_index_key(key)?;

                let base_name = get_base_identifier(obj);

                // Fill conversion: the guard rides the Integer lane, so
                // only TableKey::Int can match a fill context — a record
                // store is never fast-pathed.
                let mut fast_guard: Option<Reg<Int>> = None;
                let mut row_reserve: Option<(Reg<Ptr>, Reg<Int>)> = None;
                if let TableKey::Int(g) = key {
                    for ctx in self.fills.loop_ctxs.iter_mut().rev() {
                        if ctx.guard_reg == g.id {
                            if ctx.reserved.contains(&t_reg.id) {
                                fast_guard = Some(g);
                                break;
                            } else if let Some(name) = base_name
                                && let Some((_, bound)) =
                                    ctx.nested_fills.iter().find(|(n, _)| n == name)
                            {
                                ctx.reserved.push(t_reg.id);
                                row_reserve = Some((t_reg, *bound));
                                fast_guard = Some(g);
                                break;
                            }
                        }
                    }
                }
                if let Some((table, bound)) = row_reserve {
                    self.emit(Instruction::TableReserve { table, bound });
                }

                let store_elem = self.elem_face_of(obj)?;
                let v_reg = self.lower_expr(value, None)?.reg;
                let v_reg = if matches!(store_elem, Ty::Any) {
                    self.pack_any(v_reg)?
                } else {
                    v_reg
                };

                if let Some(ghosts) = self.shape.store_ghost_keeps.get(&stmt.id()) {
                    let row_ptr = ptr_of(v_reg)?;
                    for &g in ghosts {
                        self.ghost_keeps.insert(g, row_ptr);
                    }
                }

                if let Some(g) = fast_guard {
                    let layout = self.lookup_layout_for(obj)?;
                    self.table_set_fast(t_reg, g, v_reg, &store_elem, layout)?;
                } else {
                    self.table_set(t_reg, key, v_reg, &store_elem)?;
                }

                if matches!(value, Expr::TableCtor { .. })
                    && let Some(name) = base_name
                {
                    let bound_reg = self.fills.loop_ctxs.iter().rev().find_map(|ctx| {
                        ctx.nested_fills
                            .iter()
                            .find(|(n, _)| n == name)
                            .map(|(_, b_reg)| *b_reg)
                    });

                    if let Some(b_reg) = bound_reg {
                        self.emit(Instruction::TableReserve {
                            table: ptr_of(v_reg)?,
                            bound: b_reg,
                        });
                    }
                }

                self.null_moves_of(stmt)?;
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::While {
                condition, body, ..
            } => {
                let pre_header = self.current_block;

                let header_block = self.new_block();
                let body_block = self.new_block();
                let exit_block = self.new_block();

                // the loop's phi bases (mutation + moves, the deep
                // facts-fed scan) — the fill-conversion decision no
                // longer rides this set (H9: the walk's recorded plan
                // owns acceptance); the loop's phis still do
                let mut mutated_vars = find_mutated_vars(body, self.shape);
                mutated_vars.extend(find_moved_names(body, self.shape));

                let mut phi_order: Vec<(String, Local)> = mutated_vars
                    .iter()
                    .filter(|name| self.holds_value(name))
                    .map(|name| {
                        let local = self.read_var(name)?;
                        Ok((name.clone(), local))
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                phi_order.sort_by(|(name_a, a), (name_b, b)| {
                    (a.reg.id(), name_a).cmp(&(b.reg.id(), name_b))
                });

                let conv: Option<(String, Vec<String>, BTreeSet<String>)> = match condition {
                    Expr::BinaryOp {
                        op: BinOp::LessThan,
                        left,
                        ..
                    } if as_ident(left).is_some() => {
                        let guard = as_ident(left).expect("guarded by as_ident");
                        // H9: acceptance was decided ONCE by the walk's
                        // predicate (no break, guard born nonneg and only
                        // ascending, stable bound) and recorded as the
                        // loop's FillPlan — consumption filters stay
                        // here: the local must be live, and the base's
                        // dense verdict must match this lowering's depth
                        self.shape
                            .fill_loops
                            .get(&stmt.id())
                            .map(|plan| {
                                let depth = self.scopes.len();
                                let mut names = Vec::new();
                                for name in &plan.fills {
                                    if !self.has_var(name) {
                                        continue;
                                    }
                                    if self.shape.is_dense_at_depth(name, depth) {
                                        names.push(name.clone());
                                    }
                                }
                                (guard.to_string(), names, plan.nested_fills.clone())
                            })
                            .filter(|(_, names, nested)| !names.is_empty() || !nested.is_empty())
                    }
                    _ => None,
                };
                let conv_bound: Option<&Expr> = match condition {
                    Expr::BinaryOp {
                        op: BinOp::LessThan,
                        right: bound_expr,
                        ..
                    } if conv.is_some() => Some(bound_expr),
                    _ => None,
                };
                let mut conv_bound_reg: Option<Reg<Int>> = None;
                if let (Some((_, names, _)), Some(bound_expr)) = (&conv, conv_bound) {
                    let saved_scopes = self.scopes.clone();
                    let TypedReg { reg: b_any, .. } = self.lower_expr(bound_expr, None)?;
                    self.scopes = saved_scopes;
                    let b_reg = int_of(b_any)?;
                    conv_bound_reg = Some(b_reg);
                    for name in names {
                        let t_reg = ptr_of(self.read_var(name)?.reg)?;
                        self.emit(Instruction::TableReserve {
                            table: t_reg,
                            bound: b_reg,
                        });
                    }
                    self.emit_cond_temp_frees(stmt);
                }

                let mut phis: Vec<(String, RegId, LayoutVerdict)> = Vec::new();

                self.terminate(Terminator::Jump(header_block));
                self.current_block = header_block;

                for (var, pre_loop_local) in phi_order {
                    let phi_reg = self.next_reg();
                    let phi = phi_of(
                        repr_of(&pre_loop_local.ty),
                        phi_reg,
                        vec![(pre_header, pre_loop_local.reg)],
                    )?;
                    self.emit(Instruction::Phi(phi));
                    self.update_var(
                        &var,
                        repr_of(&pre_loop_local.ty).reg(phi_reg),
                        pre_loop_local.ty.clone(),
                        pre_loop_local.layout,
                    )?;
                    phis.push((var, phi_reg, pre_loop_local.layout));
                }

                let cond_reg = if let (Some((guard, _, _)), Some(b_reg)) = (&conv, conv_bound_reg) {
                    let g_reg = int_of(self.read_var(guard)?.reg)?;
                    let c_reg = self.next_reg();
                    self.cmp3(Instruction::Less, c_reg, g_reg, b_reg);
                    Reg::new(c_reg)
                } else {
                    let r = bool_of(self.lower_expr(condition, None)?.reg)?;
                    self.emit_cond_temp_frees(stmt);
                    r
                };
                self.terminate(Terminator::Branch {
                    cond: cond_reg,
                    true_block: body_block,
                    false_block: exit_block,
                });

                if let Some((guard, names, nested_fills)) = &conv {
                    let guard_reg = self.read_var(guard)?.reg.id();
                    let reserved = names
                        .iter()
                        .map(|name| Ok(self.read_var(name)?.reg.id()))
                        .collect::<Result<Vec<_>, LowerError>>()?;

                    let mut nested_fill_regs: Vec<(String, Reg<Int>)> = Vec::new();
                    for name in names {
                        let local = self.read_var(name)?;
                        if let Ty::Tbl(inner_ty) = &local.ty
                            && matches!(**inner_ty, Ty::Tbl(_))
                        {
                            self.emit(Instruction::TableReserve {
                                table: ptr_of(local.reg)?,
                                bound: conv_bound_reg.unwrap(),
                            });
                            nested_fill_regs.push((name.clone(), conv_bound_reg.unwrap()));
                        }
                    }
                    for name in nested_fills {
                        if self.has_var(name) {
                            let local = self.read_var(name)?;
                            if let Ty::Tbl(inner_ty) = &local.ty
                                && matches!(**inner_ty, Ty::Tbl(_))
                            {
                                self.emit(Instruction::TableReserve {
                                    table: ptr_of(local.reg)?,
                                    bound: conv_bound_reg.unwrap(),
                                });
                                nested_fill_regs.push((name.clone(), conv_bound_reg.unwrap()));
                            }
                        }
                    }

                    self.fills.loop_ctxs.push(LoopCtx {
                        guard_reg,
                        reserved,
                        nested_fills: nested_fill_regs,
                    });
                }

                self.break_ctxs.push(BreakCtx {
                    exit_block,
                    phi_vars: phis.iter().map(|(v, _, _)| v.clone()).collect(),
                    breaks: Vec::new(),
                });
                self.current_block = body_block;
                self.in_block(|an| {
                    for s in body {
                        an.lower_stmt(s)?;
                    }
                    an.emit_scope_frees((stmt.id(), 0))
                })?;
                if conv.is_some() {
                    self.fills.loop_ctxs.pop();
                }
                let break_ctx = self
                    .break_ctxs
                    .pop()
                    .expect("while lowered its body with the BreakCtx pushed");

                let end_of_body = self.current_block;
                self.terminate(Terminator::Jump(header_block));

                for (var, phi_reg, _) in &phis {
                    let back_edge_local = self.read_var(var)?;
                    for instr in &mut self.blocks[header_block].instrs {
                        if let Instruction::Phi(phi) = instr
                            && phi.target_id() == *phi_reg
                        {
                            phi_push(phi, end_of_body, back_edge_local.reg)?;
                            break;
                        }
                    }
                }

                for (var, phi_reg, pre_layout) in &phis {
                    let local = self.read_var(var)?;
                    let layout = pre_layout.join(local.layout);
                    let repr = repr_of(&local.ty);
                    self.update_var(var, repr.reg(*phi_reg), local.ty.clone(), layout)?;
                }

                self.current_block = exit_block;

                if !break_ctx.breaks.is_empty() {
                    for (i, (var, phi_reg, pre_layout)) in phis.iter().enumerate() {
                        let local = self.read_var(var)?;
                        let repr = repr_of(&local.ty);
                        let mut args = Vec::with_capacity(1 + break_ctx.breaks.len());
                        args.push((header_block, repr.reg(*phi_reg)));
                        let mut layout = pre_layout.join(local.layout);
                        for (brk_block, snap) in &break_ctx.breaks {
                            args.push((*brk_block, snap[i].reg));
                            layout = layout.join(snap[i].layout);
                        }
                        let exit_phi = self.next_reg();
                        let phi = phi_of(repr, exit_phi, args)?;
                        self.emit(Instruction::Phi(phi));
                        self.update_var(var, repr.reg(exit_phi), local.ty.clone(), layout)?;
                    }
                }
            }
            Stmt::Do { body, .. } => self.in_do(|an| -> Result<(), LowerError> {
                for s in body {
                    an.lower_stmt(s)?;
                }
                an.emit_scope_frees((stmt.id(), 0))
            })?,

            Stmt::Print { exprs, .. } => {
                let mut operands = Vec::new();
                for e in exprs {
                    let TypedReg { reg: r, ty } = self.lower_expr(e, None)?;
                    operands.push((r.id(), ty));
                }
                self.emit(Instruction::Print { operands });
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::Expr { expr, .. } => {
                self.lower_expr(expr, None)?;
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::Break { .. } => {
                // defense in depth: a break inside an expansion may only
                // bind a loop of its OWN body — the innermost ctx below
                // the expansion's base belongs to the caller and must
                // never catch an expansion's break
                if let Some(&base) = self.expansion_break_bases.last()
                    && self.break_ctxs.len() <= base
                {
                    return Err(LowerError(Diagnostic::desync(
                        "Lower Error: 'break' crossing an expansion boundary — \
                         the checker and the lowerer disagree",
                    )));
                }
                let phi_vars = self
                    .break_ctxs
                    .last()
                    .ok_or_else(|| {
                        LowerError(Diagnostic::desync(
                            "Lower Error: 'break' outside of loop — \
                             the checker and the lowerer disagree",
                        ))
                    })?
                    .phi_vars
                    .clone();
                let mut snap = Vec::with_capacity(phi_vars.len());
                for var in &phi_vars {
                    snap.push(self.read_var(var)?);
                }
                let frees = self
                    .shape
                    .break_path_frees
                    .get(&stmt.id())
                    .cloned()
                    .unwrap_or_default();
                self.emit_frees(&frees)?;
                self.emit_stmt_temp_frees(stmt);
                let ctx = self.break_ctxs.last_mut().expect("checked above");
                let exit_block = ctx.exit_block;
                ctx.breaks.push((self.current_block, snap));
                self.terminate(Terminator::Jump(exit_block));
                self.current_block = self.new_block();
            }
            Stmt::Return { value, .. } => {
                let boundary = matches!(
                    self.return_ctxs.last().map(|ctx| &ctx.kind),
                    Some(ReturnKind::Boundary)
                );
                let val_reg = if boundary {
                    match value {
                        None | Some(Expr::Nil { .. }) => {
                            let r = self.next_reg();
                            self.emit(Instruction::LoadNull {
                                target: Reg::new(r),
                            });
                            AnyReg::Ptr(Reg::new(r))
                        }
                        Some(expr) => {
                            let TypedReg { reg, .. } = self.lower_expr(expr, None)?;
                            AnyReg::Ptr(ptr_of(reg)?)
                        }
                    }
                } else {
                    match value {
                        Some(expr) if !matches!(expr, Expr::Nil { .. }) => {
                            self.lower_expr(expr, None)?.reg
                        }
                        _ => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an internal 'return' carries a value — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    }
                };
                let exit = match self.return_ctxs.last_mut().unwrap().exit {
                    Some(exit) => exit,
                    None => {
                        let exit = self.new_block();
                        self.return_ctxs.last_mut().unwrap().exit = Some(exit);
                        exit
                    }
                };
                self.return_ctxs
                    .last_mut()
                    .unwrap()
                    .args
                    .push((self.current_block, val_reg));
                let keep_frees = self
                    .shape
                    .ret_path_keep_frees
                    .get(&stmt.id())
                    .cloned()
                    .unwrap_or_default();
                let keep_temps = self
                    .shape
                    .ret_path_keep_temps
                    .get(&stmt.id())
                    .cloned()
                    .unwrap_or_default();
                if (!keep_frees.is_empty() || !keep_temps.is_empty())
                    && let Ok(keep) = ptr_of(val_reg)
                {
                    for f in &keep_frees {
                        let carrier = self.read_var(&f.carrier)?;
                        let table = ptr_of(carrier.reg)?;
                        if table.id == keep.id {
                            continue;
                        }
                        let mut keeps = vec![keep];
                        keeps.extend(self.resolve_keeps(&f.keeps)?);
                        keeps.sort_unstable_by_key(|k| k.id);
                        keeps.dedup_by_key(|k| k.id);
                        if keeps.iter().any(|k| k.id == table.id) {
                            continue;
                        }
                        signal!(trace::TRACE_RET_KEEP_FREE);
                        if keeps.len() > 1 {
                            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
                        }
                        self.emit(Instruction::TableFreeExcept { table, keeps });
                    }
                    let mut regs: Vec<Reg<Ptr>> = keep_temps
                        .iter()
                        .filter_map(|site| self.handles.site_regs.get(site).map(|(reg, _)| *reg))
                        .collect();
                    regs.sort_unstable_by_key(|reg| reg.id);
                    regs.dedup_by_key(|reg| reg.id);
                    for reg in regs.into_iter().rev() {
                        signal!(trace::TRACE_RET_KEEP_FREE);
                        self.emit(Instruction::TableFreeExcept {
                            table: reg,
                            keeps: vec![keep],
                        });
                    }
                }
                let frees = self
                    .shape
                    .ret_path_frees
                    .get(&stmt.id())
                    .cloned()
                    .unwrap_or_default();
                if !frees.is_empty() {
                    signal!(trace::TRACE_RET_PATH_FREE);
                }
                self.emit_frees(&frees)?;
                self.emit_stmt_temp_frees(stmt);
                // W3a: the creation sever's poison (a ctor return that
                // moved captures into the env zeroes the sources here)
                self.null_moves_of(stmt)?;
                self.terminate(Terminator::Jump(exit));
                self.current_block = self.new_block();
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                let cond_reg = bool_of(self.lower_expr(condition, None)?.reg)?;
                self.emit_cond_temp_frees(stmt);

                let then_block = self.new_block();
                let else_block = self.new_block();
                let join_block = self.new_block();

                self.terminate(Terminator::Branch {
                    cond: cond_reg,
                    true_block: then_block,
                    false_block: else_block,
                });

                let mut mutated = find_mutated_vars(then_body, self.shape);
                mutated.extend(find_mutated_vars(else_body, self.shape));
                mutated.extend(find_moved_names(then_body, self.shape));
                mutated.extend(find_moved_names(else_body, self.shape));
                let mutated: Vec<String> = mutated
                    .into_iter()
                    .filter(|name| self.holds_value(name))
                    .collect();

                let mut phi_order: Vec<(String, RegId)> = mutated
                    .into_iter()
                    .map(|name| {
                        let local = self.read_var(&name)?;
                        Ok((name, local.reg.id()))
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                phi_order.sort_by(|(name_a, a), (name_b, b)| (a, name_a).cmp(&(b, name_b)));

                let snapshot = self.scopes.clone();

                self.current_block = then_block;
                self.in_block(|an| {
                    for s in then_body {
                        an.lower_stmt(s)?;
                    }
                    an.emit_scope_frees((stmt.id(), 0))
                })?;
                let then_end = self.current_block;
                let then_regs: Vec<(String, AnyReg, Ty, LayoutVerdict)> = phi_order
                    .iter()
                    .map(|(name, _)| {
                        let local = self.read_var(name)?;
                        Ok((name.clone(), local.reg, local.ty, local.layout))
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                let mut then_tag: Option<Reg<Bool>> = None;
                if self.shape.join_tags.contains_key(&stmt.id()) {
                    let r = self.next_reg();
                    self.emit(Instruction::LoadBool {
                        target: Reg::new(r),
                        val: true,
                    });
                    then_tag = Some(Reg::new(r));
                }
                self.terminate(Terminator::Jump(join_block));

                self.scopes = snapshot;
                self.current_block = else_block;
                self.in_block(|an| {
                    for s in else_body {
                        an.lower_stmt(s)?;
                    }
                    an.emit_scope_frees((stmt.id(), 1))
                })?;
                let else_end = self.current_block;
                let else_regs: Vec<(String, AnyReg, Ty, LayoutVerdict)> = phi_order
                    .iter()
                    .map(|(name, _)| {
                        let local = self.read_var(name)?;
                        Ok((name.clone(), local.reg, local.ty, local.layout))
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                let mut else_tag: Option<Reg<Bool>> = None;
                if self.shape.join_tags.contains_key(&stmt.id()) {
                    let r = self.next_reg();
                    self.emit(Instruction::LoadBool {
                        target: Reg::new(r),
                        val: false,
                    });
                    else_tag = Some(Reg::new(r));
                }
                self.terminate(Terminator::Jump(join_block));

                self.current_block = join_block;
                if let (Some(t), Some(e)) = (then_tag, else_tag) {
                    let tag_reg = self.next_reg();
                    let phi = phi_of(
                        RegKind::Bool,
                        tag_reg,
                        vec![(then_end, AnyReg::Bool(t)), (else_end, AnyReg::Bool(e))],
                    )?;
                    self.emit(Instruction::Phi(phi));
                    self.if_tag_regs.insert(stmt.id(), Reg::new(tag_reg));
                }
                for (i, (name, _)) in phi_order.iter().enumerate() {
                    let phi_reg = self.next_reg();
                    let ty = join_phi_ty(&then_regs[i].2, &else_regs[i].2);
                    let joined = repr_of(&ty);
                    let layout = then_regs[i].3.join(else_regs[i].3);
                    let phi = phi_of(
                        joined,
                        phi_reg,
                        vec![(then_end, then_regs[i].1), (else_end, else_regs[i].1)],
                    )?;
                    self.emit(Instruction::Phi(phi));
                    self.update_var(name, joined.reg(phi_reg), ty, layout)?;
                }
            }
        }
        Ok(())
    }

    fn lookup_layout_for(&self, expr: &Expr) -> Result<LayoutVerdict, LowerError> {
        match expr {
            Expr::TableCtor { .. } => {
                if let Some(&site_id) = self.shape.sites.get(&expr.id()) {
                    Ok(self.shape.layouts[site_id])
                } else {
                    Ok(LayoutVerdict::default())
                }
            }
            Expr::Identifier { name, .. } => Ok(self.read_var(name)?.layout),
            Expr::Index { obj, .. } => self.lookup_layout_for(obj),
            _ => Ok(LayoutVerdict::default()),
        }
    }

    /// A dotted call lowers straight from the checker's recorded verb
    /// (signal 176 → 177): member, arity, and operand faces were all
    /// decided once upstream — this walk only sequences the operands.
    /// Operands are positional: the verb names the face, `args` carries
    /// the expressions, and both walks read the identical AST slice, so
    /// positions cannot drift. The lone guard is the missing-fact tell:
    /// a checker-accepted dotted call always carries a verb.
    fn lower_ffi_call(
        &mut self,
        call: &Expr,
        args: &[Expr],
        reg: RegId,
    ) -> Result<TypedReg, LowerError> {
        let verb = self
            .shape
            .ffi_verbs
            .get(&call.id())
            .cloned()
            .ok_or_else(|| {
                LowerError(Diagnostic::desync(
                    "Lower Error: a dotted call site carries no resolved verb — \
                     the checker and the lowerer disagree",
                ))
            })?;
        signal!(trace::TRACE_LOWER_FFI_VERB);
        match verb {
            FfiVerb::Load => {
                let path = self.lower_expr(&args[0], None)?;
                let path_reg = pooled_ptr_of(path.reg)?;
                self.emit(Instruction::FfiLoad {
                    target: Reg::new(reg),
                    path: path_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::FfiLib,
                })
            }
            FfiVerb::ArgKind => {
                let lib = self.lower_expr(&args[0], None)?;
                let lib_reg = pooled_ptr_of(lib.reg)?;
                self.emit(Instruction::FfiArgKind {
                    target: Reg::new(reg),
                    lib: lib_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::Cdef => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Ffi,
                })
            }
            FfiVerb::CoroCreate => {
                let lib = self.lower_expr(&args[0], None)?;
                let lib_reg = pooled_ptr_of(lib.reg)?;
                self.emit(Instruction::CoroCreate {
                    target: Reg::new(reg),
                    lib: lib_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::CoroResume => {
                let handle = self.lower_expr(&args[0], None)?;
                let handle_reg = int_of(handle.reg)?;
                let tbl = self.lower_expr(&args[1], None)?;
                let tbl_reg = ptr_of(tbl.reg)?;
                self.emit(Instruction::CoroResume {
                    target: Reg::new(reg),
                    handle: handle_reg,
                    args: tbl_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::CoroYield => {
                let value = self.lower_expr(&args[0], None)?;
                let value_reg = int_of(value.reg)?;
                self.emit(Instruction::CoroYield {
                    target: Reg::new(reg),
                    value: value_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::CoroStatus => {
                let handle = self.lower_expr(&args[0], None)?;
                let handle_reg = int_of(handle.reg)?;
                self.emit(Instruction::CoroStatus {
                    target: Reg::new(reg),
                    handle: handle_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Str(Reg::new(reg)),
                    ty: Ty::Str,
                })
            }
            FfiVerb::CoroClose => {
                let handle = self.lower_expr(&args[0], None)?;
                let handle_reg = int_of(handle.reg)?;
                self.emit(Instruction::CoroClose {
                    target: Reg::new(reg),
                    handle: handle_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::Drive { base, sym } => {
                let local = self.read_var(&base)?;
                let lib_reg = pooled_ptr_of(local.reg)?;
                let arg = self.lower_expr(&args[0], None)?;
                let arg_reg = ptr_of(arg.reg)?;
                self.emit(Instruction::FfiCall {
                    lib: lib_reg,
                    sym,
                    arg: arg_reg,
                });
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Ffi,
                })
            }
        }
    }

    /// W3a's ENV MINT (the Env Law, lower half): one env per creation
    /// statement — every cell a table pointer (captured tables direct,
    /// captured scalars in one-cell boxes of their own elem), so the
    /// root-exit deep free is sound on the whole tree at once. Tables
    /// MOVE in (the sources poison through the walk-booked
    /// move_poisons — the existing move law); scalars copy at mint.
    fn mint_env(&mut self, ptr: NodeId) -> Result<Reg<Ptr>, LowerError> {
        let faces: BTreeMap<String, Ty> =
            self.shape.env_faces.get(&ptr).cloned().unwrap_or_default();
        let stmt = self
            .cur_stmt
            .ok_or_else(|| LowerError(Diagnostic::lower("an env mint outside a statement")))?;
        if let Some(memo) = self.take_env_memo_for(stmt) {
            let reg = memo.reg;
            let stored = memo.stored;
            self.store_env_cells(reg, faces, stored)?;
            return Ok(reg);
        }
        let env_id = self.next_reg();
        let env = Reg::new(env_id);
        let flags = 0x01 | if faces.is_empty() { 0x00 } else { 0x80 };
        self.emit(Instruction::TableNew {
            target: env,
            elem: Ty::Str,
            flags,
        });
        self.env_regs.push(env);
        let mut stored = BTreeSet::new();
        for name in faces.keys() {
            stored.insert(name.clone());
        }
        self.store_env_cells(env, faces, BTreeSet::new())?;
        self.env_memo = Some(EnvMemo {
            stmt,
            reg: env,
            stored,
        });
        Ok(env)
    }

    fn take_env_memo_for(&mut self, stmt: NodeId) -> Option<EnvMemo> {
        if let Some(memo) = &self.env_memo
            && memo.stmt == stmt
        {
            return self.env_memo.take();
        }
        None
    }

    fn store_env_cells(
        &mut self,
        env: Reg<Ptr>,
        faces: BTreeMap<String, Ty>,
        already: BTreeSet<String>,
    ) -> Result<(), LowerError> {
        for (name, ty) in faces {
            if already.contains(&name) {
                continue;
            }
            let local = self.read_var(&name)?;
            let key = self.next_reg();
            self.emit(Instruction::StrKeyConst {
                target: Reg::new(key),
                val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
            });
            if matches!(ty, Ty::Tbl(_)) {
                let reg = ptr_of(local.reg)?;
                self.table_set(
                    env,
                    TableKey::Str(Reg::new(key)),
                    AnyReg::Ptr(reg),
                    &Ty::Str,
                )?;
            } else {
                // the scalar's box: one dense cell of its own elem
                let box_id = self.next_reg();
                let box_reg = Reg::new(box_id);
                self.emit(Instruction::TableNew {
                    target: box_reg,
                    elem: ty.clone(),
                    flags: 0,
                });
                let idx = self.next_reg();
                self.emit(Instruction::LoadInt {
                    target: Reg::new(idx),
                    val: 0,
                });
                self.table_set(box_reg, TableKey::Int(Reg::new(idx)), local.reg, &ty)?;
                self.table_set(
                    env,
                    TableKey::Str(Reg::new(key)),
                    AnyReg::Ptr(box_reg),
                    &Ty::Str,
                )?;
            }
            if let Some(memo) = &mut self.env_memo {
                memo.stored.insert(name);
            }
        }
        Ok(())
    }

    /// W3a's call-through env entry: materialize every captured name as
    /// an ordinary var (tables direct, scalars unboxed from their
    /// cells) so the body's own lowering needs no further plumbing;
    /// scalar rebinds write the box back (the Assignment arm consults
    /// `env_ctxs`).
    fn enter_env_ctx(&mut self, env: Reg<Ptr>, ptr: NodeId) -> Result<(), LowerError> {
        let faces: BTreeMap<String, Ty> =
            self.shape.env_faces.get(&ptr).cloned().unwrap_or_default();
        for (name, ty) in faces.clone() {
            let key = self.next_reg();
            self.emit(Instruction::StrKeyConst {
                target: Reg::new(key),
                val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
            });
            let cell_id = self.next_reg();
            let cell = Reg::new(cell_id);
            self.emit(Instruction::TableGet(<Ptr as CellRepr>::get(
                cell,
                env,
                TableKey::Str(Reg::new(key)),
            )));
            if matches!(ty, Ty::Tbl(_)) {
                self.declare_var(name, AnyReg::Ptr(cell), ty, LayoutVerdict::Sparse);
            } else {
                let idx = self.next_reg();
                self.emit(Instruction::LoadInt {
                    target: Reg::new(idx),
                    val: 0,
                });
                let out = self.next_reg();
                let v = self.table_get(out, cell, TableKey::Int(Reg::new(idx)), &ty);
                self.declare_var(name, v, ty, LayoutVerdict::default());
            }
        }
        self.env_ctxs.push(EnvCtx { reg: env, faces });
        Ok(())
    }

    /// The scalar write-back: a captured name's rebind lands in the env
    /// box (later calls — and siblings — read it back; L3).
    fn env_write_back(&mut self, name: &str, value: AnyReg) -> Result<(), LowerError> {
        let Some(ctx) = self.env_ctxs.last().cloned() else {
            return Ok(());
        };
        let Some(ty) = ctx.faces.get(name).cloned() else {
            return Ok(());
        };
        if matches!(ty, Ty::Tbl(_)) {
            return Ok(());
        }
        let key = self.next_reg();
        self.emit(Instruction::StrKeyConst {
            target: Reg::new(key),
            val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
        });
        let cell_id = self.next_reg();
        let cell = Reg::new(cell_id);
        self.emit(Instruction::TableGet(<Ptr as CellRepr>::get(
            cell,
            ctx.reg,
            TableKey::Str(Reg::new(key)),
        )));
        let idx = self.next_reg();
        self.emit(Instruction::LoadInt {
            target: Reg::new(idx),
            val: 0,
        });
        self.table_set(cell, TableKey::Int(Reg::new(idx)), value, &ty)?;
        Ok(())
    }

    fn lower_expr(&mut self, expr: &Expr, target: Option<RegId>) -> Result<TypedReg, LowerError> {
        let reg = target.unwrap_or_else(|| self.next_reg());

        match expr {
            Expr::Integer { value: val, .. } => {
                self.emit(Instruction::LoadInt {
                    target: Reg::new(reg),
                    val: *val,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            Expr::Float { value: val, .. } => {
                self.emit(Instruction::LoadFloat {
                    target: Reg::new(reg),
                    val: *val,
                });
                Ok(TypedReg {
                    reg: AnyReg::Float(Reg::new(reg)),
                    ty: Ty::Flt,
                })
            }
            Expr::Boolean { value: val, .. } => {
                self.emit(Instruction::LoadBool {
                    target: Reg::new(reg),
                    val: *val,
                });
                Ok(TypedReg {
                    reg: AnyReg::Bool(Reg::new(reg)),
                    ty: Ty::Bool,
                })
            }
            Expr::String { value: val, .. } => {
                self.emit(Instruction::LoadString {
                    target: Reg::new(reg),
                    val: val.clone(),
                });
                Ok(TypedReg {
                    reg: AnyReg::Str(Reg::new(reg)),
                    ty: Ty::Str,
                })
            }
            Expr::Nil { .. } => {
                unreachable!("nil outside a table release")
            }
            Expr::SysAllocCount { .. } => {
                self.emit(Instruction::SysAllocCount {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            Expr::SysExecCount { .. } => {
                self.emit(Instruction::SysExecCount {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            Expr::FfiModule { .. } => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Ffi,
                })
            }
            Expr::CoroModule { .. } => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Coro,
                })
            }
            Expr::Function { .. } => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Unknown(0),
                })
            }
            Expr::Call { callee, args, .. } => {
                // the per-instantiation fact key, derived exactly as the
                // checker derives it: the OUTERMOST expansion this call
                // is lowered inside (the call itself at no expansion)
                let call_ptr = expr.id();
                let site = self.expansion_sites.first().copied().unwrap_or(call_ptr);
                // H12/7a, ruling R1 (two-writer shadow): the lowerer's
                // ABSOLUTE loop base must be ONE OF the pair's minted
                // events' break_bases. Membership, not equality: a
                // truth-keyed pair can carry MANY events (a shared body
                // expanded twice in one extent) whose per-event bases
                // legitimately DIVERGE (h12_break_base_is_per_event_pin's
                // program), and the current event's own record is in
                // this set by construction — same walk, same order — so
                // membership never false-fires, while a base matching no
                // minted event is a checker/lowerer desync. Debug-only
                // and graceful so a checker/lowerer site desync still
                // reaches the fact-site guard below, and release bytes
                // are untouched. 7b's ordered cursor reads the event's
                // OWN record and retires this check with the stacks.
                if let Some(&owner) = self.shape.instance_of.get(&(call_ptr, site))
                    && let Some(owner_rec) = self.shape.instances.get(&owner)
                    && let Some(kids) = owner_rec.children.get(&call_ptr)
                {
                    debug_assert!(
                        kids.iter().any(|k| {
                            self.shape
                                .instances
                                .get(k)
                                .is_some_and(|rec| rec.break_base == self.break_ctxs.len())
                        }),
                        "the shadow (7a): the lowerer's break base matches no \
                         minted event — the checker and the lowerer disagree"
                    );
                }
                // D4 precedence, lower half: a Field callee is a module
                // surface call UNLESS the checker resolved it as an
                // expansion (call_defs carries the decision — the lowerer
                // never re-derives precedence)
                if let Expr::Field { .. } = callee.as_ref()
                    && !self.shape.call_defs.contains_key(&(call_ptr, site))
                {
                    return self.lower_ffi_call(expr, args, reg);
                }
                let fn_ptr = self
                    .shape
                    .call_defs
                    .get(&(call_ptr, site))
                    .copied()
                    .ok_or_else(|| {
                        LowerError(Diagnostic::desync(
                            "Lower Error: a call site with no resolved function — \
                             the checker and the lowerer disagree",
                        ))
                    })?;
                // W3a's dispatch, lower half: a call-through reads the
                // closure VALUE's register — the env pointer. An
                // Identifier callee whose binding carries a Closure type
                // dispatches off the binding's own register; a Field
                // callee reads the record cell ONLY when the checker
                // recorded a closure dispatch — a D4 dot-ns expansion
                // call rides the same callee shape and reads nothing.
                let call_env: Option<Reg<Ptr>> = match callee.as_ref() {
                    Expr::Identifier { name: n, .. } => match self.read_var(n) {
                        Ok(local) if matches!(local.ty, Ty::Closure(_)) => Some(ptr_of(local.reg)?),
                        _ => None,
                    },
                    Expr::Field { obj, name, .. }
                        if self.shape.closure_calls.contains(&(call_ptr, site)) =>
                    {
                        let t_any = self.lower_expr(obj, None)?.reg;
                        let t_reg = ptr_of(t_any)?;
                        let k = self.next_reg();
                        self.emit(Instruction::StrKeyConst {
                            target: Reg::new(k),
                            val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
                        });
                        let cell = self.next_reg();
                        self.emit(Instruction::TableGet(<Ptr as CellRepr>::get(
                            Reg::new(cell),
                            t_reg,
                            TableKey::Str(Reg::new(k)),
                        )));
                        Some(Reg::new(cell))
                    }
                    _ => None,
                };
                if self.inline_stack.contains(&fn_ptr) {
                    return Err(LowerError(Diagnostic::desync(
                        "Lower Error: recursive inlining — \
                         the checker and the lowerer disagree",
                    )));
                }
                let def = self.shape.fn_defs.get(&fn_ptr).cloned().ok_or_else(|| {
                    LowerError(Diagnostic::desync(
                        "Lower Error: a call site names a function with no body — \
                         the checker and the lowerer disagree",
                    ))
                })?;
                let call_ret = self
                    .shape
                    .call_rets
                    .get(&(call_ptr, site))
                    .cloned()
                    .ok_or_else(|| {
                        LowerError(Diagnostic::desync(
                            "Lower Error: a call site with no resolved return — \
                             the checker and the lowerer disagree",
                        ))
                    })?;
                let scope_key = self.shape.fn_scope_keys.get(&fn_ptr).copied();
                let body = def.body();

                let mut arg_regs = Vec::with_capacity(args.len());
                for a in args {
                    let tr = self.lower_expr(a, None)?;
                    let layout = self.lookup_layout_for(a)?;
                    arg_regs.push((tr, layout));
                }

                self.inline_stack.push(fn_ptr);
                self.expansion_sites.push(call_ptr);
                self.expansion_break_bases.push(self.break_ctxs.len());
                self.return_ctxs.push(ReturnCtx {
                    kind: ReturnKind::Inline {
                        ty: call_ret.clone(),
                    },
                    exit: None,
                    args: Vec::new(),
                });
                self.in_block(|an| {
                    for (p, (tr, layout)) in def.params.iter().zip(arg_regs) {
                        an.declare_var(p.clone(), tr.reg, tr.ty, layout);
                    }
                    // W3a: the call-through materializes its captures as
                    // ordinary vars off the env (inside this block's
                    // scope — they die with the expansion)
                    if let Some(env) = call_env {
                        an.enter_env_ctx(env, fn_ptr)?;
                    }
                    for s in body {
                        an.lower_stmt(s)?;
                    }
                    match scope_key {
                        Some(key) => an.emit_scope_frees(key),
                        None => Ok(()),
                    }
                })?;
                let result = self.finalize_return_ctx()?.ok_or_else(|| {
                    LowerError(Diagnostic::desync(
                        "Lower Error: an inline call produced no value — \
                         the checker and the lowerer disagree",
                    ))
                })?;
                if let Some(classes) = self.shape.call_tags.get(&expr.id()).cloned() {
                    let exit = self.current_block;
                    let edge_blocks: Vec<BlockId> = self.blocks[exit]
                        .instrs
                        .iter()
                        .find_map(|i| match i {
                            Instruction::Phi(p) => Some(p.arg_blocks().to_vec()),
                            _ => None,
                        })
                        .unwrap_or_default();
                    if edge_blocks.len() < classes.len() {
                        return Err(LowerError(Diagnostic::desync(
                            "Lower Error: a tagged call's return edges went missing — \
                             the analyzer and the lowerer disagree",
                        )));
                    }
                    let mut tag_args: Vec<(BlockId, AnyReg)> = Vec::new();
                    for (i, &b) in edge_blocks.iter().enumerate() {
                        let class = classes.get(i).copied().unwrap_or(false);
                        let r = self.next_reg();
                        let block = &mut self.blocks[b];
                        block.locs.push(self.cur_loc);
                        block.instrs.push(Instruction::LoadBool {
                            target: Reg::new(r),
                            val: class,
                        });
                        tag_args.push((b, AnyReg::Bool(Reg::new(r))));
                    }
                    let tag_reg = self.next_reg();
                    let phi = phi_of(RegKind::Bool, tag_reg, tag_args)?;
                    self.emit(Instruction::Phi(phi));
                    self.call_tag_regs.insert(expr.id(), Reg::new(tag_reg));
                }
                self.inline_stack.pop();
                self.expansion_sites.pop();
                self.expansion_break_bases.pop();
                if call_env.is_some() {
                    self.env_ctxs.pop();
                }
                Ok(TypedReg {
                    reg: result,
                    ty: call_ret,
                })
            }
            Expr::TableCtor { entries, .. } => {
                let elem = self.shape.elem_of(expr);
                let ctor_site = self.shape.sites.get(&expr.id()).copied();

                // W3a, R3: which fields carry closure faces — their
                // stores ride the Ptr lane and the table's own cells go
                // 8-byte (a closure record's non-closure fields must be
                // Int/Flt/Str; the checker's R3 field-kind rule rejects
                // the rest at the ctor — pinned by
                // escape_record_bool_field_rejected and
                // escape_record_table_field_rejected, folded 2026-10-27
                // after the elem join was shown NOT to reject them: a
                // Bool/Any cell aborted at runtime on the mis-sized
                // record, a table cell double-freed)
                let has_closure_fields = entries.iter().any(|(k, _)| match k {
                    CtorKey::Str(n) => ctor_site
                        .is_some_and(|s| self.shape.closure_fields.contains_key(&(s, n.clone()))),
                    _ => false,
                });

                if matches!(elem, crate::shape::Ty::Unknown(_)) {
                    signal!(trace::TRACE_TABLE_NEW_UNDECIDED);
                }

                let mut has_inline_tables = false;
                for (_, e) in entries {
                    if matches!(e, Expr::TableCtor { .. }) {
                        has_inline_tables = true;
                    }
                }

                let is_stored_parent =
                    ctor_site.is_some_and(|s| self.shape.stored_ctor_parents.contains(&s));

                let contains_tables = matches!(elem, crate::shape::Ty::Tbl(_))
                    && (has_inline_tables || is_stored_parent);

                let mut elem_regs = Vec::with_capacity(entries.len());
                for (key, e) in entries {
                    let TypedReg { reg: r, .. } = self.lower_expr(e, None)?;
                    // a closure field's cell rides the Ptr lane raw —
                    // never packed into an Any elem
                    let is_closure_field = match key {
                        CtorKey::Str(n) => ctor_site.is_some_and(|s| {
                            self.shape.closure_fields.contains_key(&(s, n.clone()))
                        }),
                        _ => false,
                    };
                    let r = if matches!(elem, Ty::Any) && !is_closure_field {
                        self.pack_any(r)?
                    } else {
                        r
                    };
                    elem_regs.push(r);
                }

                if let Some(pairs) = self.shape.ctor_ghost_keeps.get(&expr.id()) {
                    for &(ei, g) in pairs {
                        if let Some(&r) = elem_regs.get(ei)
                            && let Ok(ptr) = ptr_of(r)
                        {
                            self.ghost_keeps.insert(g, ptr);
                        }
                    }
                }

                let mode_bit = match self.lookup_layout_for(expr)? {
                    crate::shape::LayoutVerdict::Sparse => 0x01,
                    _ => 0x00,
                };
                let flags = mode_bit | if contains_tables { 0x80 } else { 0x00 };

                let tbl = Reg::<Ptr>::new(reg);
                // W3a: a closure record's cells are 8-byte (Ptr-lane raw
                // stores share the buffer with Int/Flt/Str fields)
                let new_elem = if has_closure_fields {
                    Ty::Str
                } else {
                    elem.clone()
                };
                self.emit(Instruction::TableNew {
                    target: tbl,
                    elem: new_elem,
                    flags,
                });
                if let Some(&site) = self.shape.sites.get(&expr.id()) {
                    self.handles.site_regs.insert(site, (tbl, self.ctrl_depth));
                }
                for ((key, _), v_reg) in entries.iter().zip(elem_regs) {
                    match key {
                        CtorKey::Const(slot) => {
                            let i_reg = self.next_reg();
                            self.emit(Instruction::LoadInt {
                                target: Reg::new(i_reg),
                                val: *slot,
                            });
                            self.table_set(tbl, TableKey::Int(Reg::new(i_reg)), v_reg, &elem)?;
                        }
                        CtorKey::Str(name) => {
                            let k = self.next_reg();
                            self.emit(Instruction::StrKeyConst {
                                target: Reg::new(k),
                                val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
                            });
                            // W3a, R3: the closure face rides the field —
                            // its cell stores the env pointer raw
                            let store_face = match ctor_site
                                .and_then(|s| self.shape.closure_fields.get(&(s, name.clone())))
                            {
                                Some(&ptr) => Ty::Closure(ptr),
                                None => elem.clone(),
                            };
                            self.table_set(tbl, TableKey::Str(Reg::new(k)), v_reg, &store_face)?;
                        }
                        CtorKey::Expr(ke) => {
                            // the checker runs check_index_key on ctor keys —
                            // String keys are legal and lower to StrKey
                            let key = self.lower_index_key(ke)?;
                            self.table_set(tbl, key, v_reg, &elem)?;
                        }
                    }
                }
                Ok(TypedReg {
                    reg: AnyReg::Ptr(tbl),
                    ty: Ty::Tbl(Box::new(elem)),
                })
            }
            Expr::Index { obj, key, .. } => {
                let t_any = self.lower_expr(obj, None)?.reg;
                let key = self.lower_index_key(key)?;
                let target_ty = self.elem_face_of(obj)?;
                let t_reg = ptr_of(t_any)?;
                let out = self.table_get(reg, t_reg, key, &target_ty);
                Ok(TypedReg {
                    reg: out,
                    ty: target_ty,
                })
            }
            Expr::Field { obj, name, .. } => {
                // Non-callee dot access is a record read: identical to
                // t["name"]. Inlined rather than delegated to a synthetic
                // Index expr, whose clone would allocate a fresh operand
                // the checker never walked. Register order: the get
                // target is allocated before the operand (an untargeted
                // field access still burns its entry register).
                let get_reg = if target.is_some() {
                    reg
                } else {
                    self.next_reg()
                };
                let TypedReg { reg: t_any, .. } = self.lower_expr(obj, None)?;
                let k = self.next_reg();
                self.emit(Instruction::StrKeyConst {
                    target: Reg::new(k),
                    val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
                });
                let target_ty = self.elem_face_of(obj)?;
                let t_reg = ptr_of(t_any)?;
                let out = self.table_get(get_reg, t_reg, TableKey::Str(Reg::new(k)), &target_ty);
                Ok(TypedReg {
                    reg: out,
                    ty: target_ty,
                })
            }
            Expr::Identifier { name, .. } => {
                // W3a's creation: a fn name read as a value mints (or
                // joins) this statement's env and answers the env
                // pointer — a closure value's register IS its env.
                let site = self.fact_site(expr.id());
                if let Some(&ptr) = self.shape.creation_envs.get(&(expr.id(), site)) {
                    let reg = self.mint_env(ptr)?;
                    return Ok(TypedReg {
                        reg: AnyReg::Ptr(reg),
                        ty: Ty::Closure(ptr),
                    });
                }
                let local = self.read_var(name)?;
                if target.is_some() && reg != local.reg.id() {
                    let moved = self.emit_move_into(reg, local.reg);
                    Ok(TypedReg {
                        reg: moved,
                        ty: local.ty,
                    })
                } else {
                    Ok(TypedReg {
                        reg: local.reg,
                        ty: local.ty,
                    })
                }
            }
            Expr::BinaryOp {
                op: op @ (BinOp::And | BinOp::Or),
                left,
                right,
                ..
            } => {
                let l_reg = bool_of(self.lower_expr(left, None)?.reg)?;
                self.emit_arm_temp_frees(left);
                let then_block = self.new_block();
                let else_block = self.new_block();
                let join_block = self.new_block();
                self.terminate(Terminator::Branch {
                    cond: l_reg,
                    true_block: then_block,
                    false_block: else_block,
                });
                let and_op = matches!(op, BinOp::And);
                let (value_block, const_block, short_val) = if and_op {
                    (then_block, else_block, false)
                } else {
                    (else_block, then_block, true)
                };

                self.current_block = value_block;
                let v_reg = self.at_depth(|an| an.lower_expr(right, None))?.reg;
                let value_end = self.current_block;
                self.emit_arm_temp_frees(right);
                self.terminate(Terminator::Jump(join_block));

                self.current_block = const_block;
                let c_reg = self.next_reg();
                self.emit(Instruction::LoadBool {
                    target: Reg::new(c_reg),
                    val: short_val,
                });
                let const_end = const_block;
                self.terminate(Terminator::Jump(join_block));

                self.current_block = join_block;
                let (t_end, t_reg, e_end, e_reg) = if and_op {
                    (value_end, v_reg, const_end, AnyReg::Bool(Reg::new(c_reg)))
                } else {
                    (const_end, AnyReg::Bool(Reg::new(c_reg)), value_end, v_reg)
                };
                let phi = phi_of(RegKind::Bool, reg, vec![(t_end, t_reg), (e_end, e_reg)])?;
                self.emit(Instruction::Phi(phi));
                Ok(TypedReg {
                    reg: AnyReg::Bool(Reg::new(reg)),
                    ty: Ty::Bool,
                })
            }
            Expr::BinaryOp {
                op, left, right, ..
            } => {
                let TypedReg {
                    reg: l_any,
                    ty: l_ty,
                } = self.lower_expr(left, None)?;
                let TypedReg {
                    reg: r_any,
                    ty: r_ty,
                } = self.lower_expr(right, None)?;
                match op {
                    BinOp::Add => match num_pair(l_any, r_any)? {
                        NumPair::II(a, b) => self.num3(Instruction::Add, reg, a, b),
                        NumPair::FF(a, b) => self.num3(Instruction::Add, reg, a, b),
                    },
                    BinOp::Sub => match num_pair(l_any, r_any)? {
                        NumPair::II(a, b) => self.num3(Instruction::Sub, reg, a, b),
                        NumPair::FF(a, b) => self.num3(Instruction::Sub, reg, a, b),
                    },
                    BinOp::Mul => match num_pair(l_any, r_any)? {
                        NumPair::II(a, b) => self.num3(Instruction::Mul, reg, a, b),
                        NumPair::FF(a, b) => self.num3(Instruction::Mul, reg, a, b),
                    },
                    BinOp::Div => {
                        let l_reg = self.promote_to_float(l_any, &l_ty)?;
                        let r_reg = self.promote_to_float(r_any, &r_ty)?;
                        self.emit(Instruction::Div {
                            target: Reg::new(reg),
                            left: l_reg,
                            right: r_reg,
                        });
                    }
                    BinOp::IntDiv => {
                        let rhs_const = const_of(right);
                        match num_pair(l_any, r_any)? {
                            NumPair::II(a, b) => {
                                self.num3r(Instruction::IntDiv, reg, a, b, rhs_const)
                            }
                            NumPair::FF(a, b) => {
                                self.num3r(Instruction::IntDiv, reg, a, b, rhs_const)
                            }
                        }
                    }
                    BinOp::Mod => {
                        let rhs_const = const_of(right);
                        match num_pair(l_any, r_any)? {
                            NumPair::II(a, b) => self.num3r(Instruction::Mod, reg, a, b, rhs_const),
                            NumPair::FF(a, b) => self.num3r(Instruction::Mod, reg, a, b, rhs_const),
                        }
                    }
                    BinOp::LessThan => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::AA(..) => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an ordering comparison on Any boundary cells — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    },
                    BinOp::GreaterThan => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::AA(..) => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an ordering comparison on Any boundary cells — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    },
                    BinOp::LessEq => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::AA(..) => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an ordering comparison on Any boundary cells — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    },
                    BinOp::GreaterEq => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::AA(..) => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an ordering comparison on Any boundary cells — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    },
                    BinOp::Equal => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::AA(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                    },
                    BinOp::NotEqual => {
                        let e = self.next_reg();
                        match ord_pair(l_any, r_any)? {
                            OrdPair::II(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::FF(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::BB(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::SS(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::PP(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::AA(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                        }
                        self.emit(Instruction::Not {
                            target: Reg::new(reg),
                            source: Reg::new(e),
                        });
                    }
                    BinOp::And | BinOp::Or => unreachable!(),
                }
                let ty = match op {
                    BinOp::LessThan
                    | BinOp::GreaterThan
                    | BinOp::LessEq
                    | BinOp::GreaterEq
                    | BinOp::Equal
                    | BinOp::NotEqual => Ty::Bool,
                    BinOp::Div => Ty::Flt,
                    _ => {
                        if matches!(l_ty, Ty::Flt) || matches!(r_ty, Ty::Flt) {
                            Ty::Flt
                        } else {
                            Ty::Int
                        }
                    }
                };
                Ok(TypedReg {
                    reg: repr_of(&ty).reg(reg),
                    ty,
                })
            }
            Expr::UnaryOp { op, expr, .. } => match op {
                UnOp::Neg => {
                    let TypedReg {
                        reg: x_any,
                        ty: x_ty,
                    } = self.lower_expr(expr, None)?;
                    let out = match num_single(x_any)? {
                        NumSingle::I(x) => {
                            self.neg1(reg, x);
                            AnyReg::Int(Reg::new(reg))
                        }
                        NumSingle::F(x) => {
                            self.neg1(reg, x);
                            AnyReg::Float(Reg::new(reg))
                        }
                    };
                    Ok(TypedReg { reg: out, ty: x_ty })
                }
                UnOp::Not => {
                    let x_reg = bool_of(self.lower_expr(expr, None)?.reg)?;
                    self.emit(Instruction::Not {
                        target: Reg::new(reg),
                        source: x_reg,
                    });
                    Ok(TypedReg {
                        reg: AnyReg::Bool(Reg::new(reg)),
                        ty: Ty::Bool,
                    })
                }
                UnOp::Len => {
                    if let Expr::String { value: s, .. } = expr.as_ref() {
                        self.emit(Instruction::LoadInt {
                            target: Reg::new(reg),
                            val: s.len() as i64,
                        });
                        return Ok(TypedReg {
                            reg: AnyReg::Int(Reg::new(reg)),
                            ty: Ty::Int,
                        });
                    }
                    let TypedReg { reg: v, ty } = self.lower_expr(expr, None)?;
                    match ty {
                        Ty::Str => {
                            let s_reg = str_lane(v)?;
                            self.emit(Instruction::StrLen {
                                target: Reg::new(reg),
                                s: s_reg,
                            });
                            Ok(TypedReg {
                                reg: AnyReg::Int(Reg::new(reg)),
                                ty: Ty::Int,
                            })
                        }
                        Ty::Any => {
                            let a_reg = any_of(v)?;
                            self.emit(Instruction::AnyLen {
                                target: Reg::new(reg),
                                source: a_reg,
                            });
                            Ok(TypedReg {
                                reg: AnyReg::Int(Reg::new(reg)),
                                ty: Ty::Int,
                            })
                        }
                        Ty::Tbl(_) | Ty::Unknown(_) => {
                            let t_reg = ptr_of(v)?;
                            self.emit(Instruction::TableLen {
                                target: Reg::new(reg),
                                table: t_reg,
                            });
                            Ok(TypedReg {
                                reg: AnyReg::Int(Reg::new(reg)),
                                ty: Ty::Int,
                            })
                        }
                        _ => Err(LowerError(Diagnostic::desync(
                            "Lower Error: '#' requires a String, table, or Any operand — \
                             the checker and the lowerer disagree",
                        ))),
                    }
                }
            },
        }
    }
}

fn const_of(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Integer { value: v, .. } => Some(*v),
        _ => None,
    }
}

fn find_moved_names(stmts: &[Stmt], shape: &ShapeFacts) -> BTreeSet<String> {
    let mut moved = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for stmt in stmts {
        if let Some(names) = shape.move_poisons.get(&stmt.id()) {
            moved.extend(names.iter().cloned());
        }
        stmt_call_touched(stmt, shape, &mut moved, &mut seen);
        match stmt {
            Stmt::While { body, .. } | Stmt::Do { body, .. } => {
                moved.extend(find_moved_names(body, shape));
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                moved.extend(find_moved_names(then_body, shape));
                moved.extend(find_moved_names(else_body, shape));
            }
            _ => {}
        }
    }
    moved
}

fn calls_touched(
    expr: &Expr,
    shape: &ShapeFacts,
    out: &mut BTreeSet<String>,
    seen: &mut BTreeSet<NodeId>,
) {
    match expr {
        Expr::Call { callee, args, .. } => {
            // union read: every instantiation of this call expr (all its
            // expansion sites) contributes its fn's touched names — the
            // order-insensitive consumer the per-instantiation keys were
            // designed to leave alone
            let key = expr.id();
            for (_, &fn_ptr) in shape
                .call_defs
                .range((key, NodeId(0))..=(key, NodeId(u32::MAX)))
            {
                if let Some(touched) = shape.fn_touched.get(&fn_ptr) {
                    out.extend(touched.iter().cloned());
                }
                // THE TRANSITIVE CLOSURE: `fn_touched` is the per-fn law
                // (a fn's own lexical outer touches — the derivation
                // pass's scan; a callee's set lives under its own id and
                // never propagates into its caller's). A chain G→H
                // assigning an outer name must therefore reach the set
                // through the MIDDLE call: walk the callee's OWNED BODY
                // (H6's self-contained facts) with the same walker. The
                // checker refuses recursive inlining, so the call graph
                // is a DAG on every compile that reaches the lowerer;
                // `seen` is the walk's convergence face and its defense
                // in depth.
                if seen.insert(fn_ptr)
                    && let Some(def) = shape.fn_defs.get(&fn_ptr)
                {
                    fn_stmts_touched(def.body(), shape, out, seen);
                }
            }
            calls_touched(callee, shape, out, seen);
            for a in args {
                calls_touched(a, shape, out, seen);
            }
        }
        Expr::BinaryOp { left, right, .. } => {
            calls_touched(left, shape, out, seen);
            calls_touched(right, shape, out, seen);
        }
        Expr::UnaryOp { expr, .. } => calls_touched(expr, shape, out, seen),
        Expr::Index { obj, key, .. } => {
            calls_touched(obj, shape, out, seen);
            calls_touched(key, shape, out, seen);
        }
        Expr::Field { obj, .. } => calls_touched(obj, shape, out, seen),
        Expr::TableCtor { entries, .. } => {
            for (k, v) in entries {
                if let CtorKey::Expr(ke) = k {
                    calls_touched(ke, shape, out, seen);
                }
                calls_touched(v, shape, out, seen);
            }
        }
        _ => {}
    }
}

/// The transitive closure's body walker: one fn's owned body, every
/// statement face (nested loops and branches included), every call
/// routed back through `calls_touched` so the chain keeps walking.
fn fn_stmts_touched(
    stmts: &[Stmt],
    shape: &ShapeFacts,
    out: &mut BTreeSet<String>,
    seen: &mut BTreeSet<NodeId>,
) {
    for s in stmts {
        stmt_call_touched(s, shape, out, seen);
        match s {
            Stmt::While { body, .. } | Stmt::Do { body, .. } => {
                fn_stmts_touched(body, shape, out, seen);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                fn_stmts_touched(then_body, shape, out, seen);
                fn_stmts_touched(else_body, shape, out, seen);
            }
            _ => {}
        }
    }
}

/// Every expression face one statement carries, swept for calls. The
/// loop-phi collectors ride this on EVERY statement shape: the pre-fold
/// scan reached `calls_touched` only from `Stmt::Expr`, so a call in
/// any value position (`local c = H()`, `c = H()`, `print(H())`, a
/// condition, a return value) contributed nothing — an outer name
/// assigned through such a call never joined the loop's phi set, the
/// loop body read the pre-loop register every iteration, and a
/// post-loop read was an undominated use (the backend aborted on a
/// legal program; without the read the loop's writes were silently
/// lost). Over-approximation is the safe direction here: a name in the
/// phi set whose register never changes mints a degenerate phi, never
/// a wrong answer.
fn stmt_call_touched(
    stmt: &Stmt,
    shape: &ShapeFacts,
    out: &mut BTreeSet<String>,
    seen: &mut BTreeSet<NodeId>,
) {
    match stmt {
        Stmt::LocalDecl { exprs, .. } | Stmt::Print { exprs, .. } => {
            for e in exprs {
                calls_touched(e, shape, out, seen);
            }
        }
        Stmt::Assignment { expr, .. } => calls_touched(expr, shape, out, seen),
        Stmt::IndexAssign {
            obj, key, value, ..
        } => {
            calls_touched(obj, shape, out, seen);
            calls_touched(key, shape, out, seen);
            calls_touched(value, shape, out, seen);
        }
        Stmt::While { condition, .. } => calls_touched(condition, shape, out, seen),
        Stmt::If { condition, .. } => calls_touched(condition, shape, out, seen),
        Stmt::Expr { expr, .. } => calls_touched(expr, shape, out, seen),
        Stmt::Return { value: Some(e), .. } => calls_touched(e, shape, out, seen),
        _ => {}
    }
}

fn find_mutated_vars(stmts: &[Stmt], shape: &ShapeFacts) -> BTreeSet<String> {
    let mut mutated = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for stmt in stmts {
        stmt_call_touched(stmt, shape, &mut mutated, &mut seen);
        match stmt {
            Stmt::Assignment { name, .. } => {
                mutated.insert(name.clone());
            }
            Stmt::While { body, .. } => {
                mutated.extend(find_mutated_vars(body, shape));
            }
            Stmt::Do { body, .. } => {
                mutated.extend(find_mutated_vars(body, shape));
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                mutated.extend(find_mutated_vars(then_body, shape));
                mutated.extend(find_mutated_vars(else_body, shape));
            }
            _ => {}
        }
    }
    mutated
}

fn as_ident(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Identifier { name, .. } => Some(name),
        _ => None,
    }
}

fn get_base_identifier(expr: &Expr) -> Option<&String> {
    match expr {
        Expr::Identifier { name, .. } => Some(name),
        Expr::Index { obj, .. } => get_base_identifier(obj),
        _ => None,
    }
}

/// H11: the desync protocol is a VARIANT — `Diagnostic::desync` mints
/// it, `is_desync` matches the kind, and the rendered tail ("… — the
/// halves disagree") stays the protocol's observable face (H12's 7c
/// deletes both with the class). These tests are the substring era's
/// successor: the old `contains("disagree")` classifier pinned the
/// TEXT; the variant pins the MINT.
#[cfg(test)]
mod desync_class_tests {
    use super::LowerError;
    use crate::diag::Diagnostic;

    /// The real desync message texts, minted as the protocol demands —
    /// each classifies structurally, and each still renders its tail
    /// (the disagreeing halves are message content, not format).
    #[test]
    fn desync_mints_classify_and_render_the_tail() {
        for msg in [
            Diagnostic::desync(
                "Lower Error: a table operand position received a non-table — \
             the checker and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: a housed row's keep register was never \
             captured — the analyzer and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: IR emitter label desync: a br/phi names block 'b3', \
             which the module never emits — the emitters and the block \
             model disagree (see SeamPlan in backend.rs)",
            ),
            Diagnostic::desync(
                "Lower Error: a dotted call site carries no resolved verb — \
             the checker and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: an index key carries no recorded lane — \
             the checker and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: a table access carries no recorded elem face — \
             the checker and the lowerer disagree",
            ),
            Diagnostic::desync(
                "Lower Error: a string operand position received a different repr — \
             the checker and the lowerer disagree",
            ),
        ] {
            assert!(LowerError(msg.clone()).is_desync(), "{msg}");
            assert!(msg.render().contains("disagree"), "{msg}");
        }
    }

    /// The substring era's false-positive class is unrepresentable: a
    /// message whose TEXT merely contains "disagree" is not a desync
    /// unless minted as one — script errors never are.
    #[test]
    fn desync_is_the_mint_not_the_bytes() {
        for msg in [
            Diagnostic::lower("Undeclared variable"),
            Diagnostic::lower("the operands disagree with the repr table"),
        ] {
            assert!(!LowerError(msg.clone()).is_desync(), "{msg}");
        }
        assert!(!LowerError(Diagnostic::lower("plain")).is_desync());
        assert!(LowerError(Diagnostic::desync("any bespoke bug text")).is_desync());
    }
}

#[cfg(test)]
mod break_gate_tests {
    use crate::ast::has_break;
    use crate::ast::{Expr, Loc, NodeId, Stmt};

    fn at() -> Loc {
        Loc { line: 1, col: 1 }
    }

    fn assign_i() -> Stmt {
        Stmt::Assignment {
            name: "i".to_string(),
            expr: Expr::Integer {
                value: 1,
                id: NodeId::mint(),
            },
            loc: at(),
            id: NodeId::mint(),
        }
    }

    #[test]
    fn flat_break_is_this_loops() {
        assert!(has_break(&[Stmt::Break {
            loc: at(),
            id: NodeId::mint()
        }]));
        assert!(!has_break(&[assign_i()]));
    }

    #[test]
    fn break_through_do_and_if_counts() {
        let cond = Expr::Boolean {
            value: true,
            id: NodeId::mint(),
        };
        let brk = vec![Stmt::Break {
            loc: at(),
            id: NodeId::mint(),
        }];
        assert!(has_break(&[Stmt::Do {
            body: brk.clone(),
            loc: at(),
            id: NodeId::mint()
        }]));
        assert!(has_break(&[Stmt::If {
            condition: cond.clone(),
            then_body: brk.clone(),
            else_body: vec![],
            loc: at(),
            id: NodeId::mint()
        }]));
        assert!(has_break(&[Stmt::If {
            condition: cond,
            then_body: vec![],
            else_body: brk,
            loc: at(),
            id: NodeId::mint()
        }]));
    }

    #[test]
    fn break_inside_nested_while_binds_to_the_inner_loop() {
        let nested = vec![Stmt::While {
            condition: Expr::Boolean {
                value: true,
                id: NodeId::mint(),
            },
            body: vec![Stmt::Break {
                loc: at(),
                id: NodeId::mint(),
            }],
            loc: at(),
            id: NodeId::mint(),
        }];
        assert!(!has_break(&nested));
    }

    #[test]
    fn break_inside_a_function_body_is_not_this_loops() {
        // R8's AST half: has_break does not recurse into Expr::Function —
        // a body's break binds to a loop written in THAT body, never to
        // the loop enclosing the definition. The walk's cross-boundary
        // gate and the lowerer's BreakCtx base guard this same law.
        let fn_with_break = Stmt::LocalDecl {
            names: vec!["f".to_string()],
            exprs: vec![Expr::Function {
                params: vec![],
                body: vec![Stmt::Break {
                    loc: at(),
                    id: NodeId::mint(),
                }],
                id: NodeId::mint(),
            }],
            loc: at(),
            id: NodeId::mint(),
        };
        assert!(!has_break(&[fn_with_break]));

        let fn_with_own_loop = Stmt::LocalDecl {
            names: vec!["f".to_string()],
            exprs: vec![Expr::Function {
                params: vec![],
                body: vec![Stmt::While {
                    condition: Expr::Boolean {
                        value: true,
                        id: NodeId::mint(),
                    },
                    body: vec![Stmt::Break {
                        loc: at(),
                        id: NodeId::mint(),
                    }],
                    loc: at(),
                    id: NodeId::mint(),
                }],
                id: NodeId::mint(),
            }],
            loc: at(),
            id: NodeId::mint(),
        };
        assert!(!has_break(&[fn_with_own_loop]));
    }
}
