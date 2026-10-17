use super::{IrLowerer, LowerError};

use crate::ir::{
    Any, AnyReg, BlockId, Bool, Byte, CellRepr, CellTy, CellVal, CmpRegs, CmpRepr, Float,
    Instruction, Int, MoveRegs, NumRegs, NumRegsRhs, NumRepr, PackRegs, PhiRegs, PhiRepr, Ptr, Reg,
    RegKind, TableKey, Terminator,
};
use crate::shape::Ty;
pub(super) fn int_of(r: AnyReg) -> Result<Reg<Int>, LowerError> {
    match r {
        AnyReg::Int(x) => Ok(x),
        _ => Err(repr_mismatch("an Integer operand position")),
    }
}

pub(super) fn float_of(r: AnyReg) -> Result<Reg<Float>, LowerError> {
    match r {
        AnyReg::Float(x) => Ok(x),
        _ => Err(repr_mismatch("a Float operand position")),
    }
}

pub(super) fn bool_of(r: AnyReg) -> Result<Reg<Bool>, LowerError> {
    match r {
        AnyReg::Bool(x) => Ok(x),
        _ => Err(repr_mismatch("a Bool operand position")),
    }
}

pub(super) fn ptr_of(r: AnyReg) -> Result<Reg<Ptr>, LowerError> {
    match r {
        AnyReg::Ptr(x) => Ok(x),
        _ => {
            crate::glm_dbgln!("[lower] ptr_of got {r:?}");
            Err(repr_mismatch("a table-header operand position"))
        }
    }
}

/// The pooled-handle dual: a String-typed value may physically carry
/// either string face — Str (a literal, a normalized binding) or Ptr
/// (a cell read, a phi, a zero value) — and both are the same pooled
/// pointer. ONE definition for every consumer that needs the string
/// register behind a string-ish operand; the remaining arms are the
/// desync tell (a non-pointer repr in a String position).
pub(super) fn str_lane(r: AnyReg) -> Result<Reg<crate::ir::Str>, LowerError> {
    match r {
        AnyReg::Str(s) => Ok(s),
        AnyReg::Ptr(p) => Ok(Reg::new(p.id)),
        _ => Err(repr_mismatch("a string operand position")),
    }
}

/// The same dual, pointer face: for consumers that want the raw pool
/// handle (ffi lanes, pointer comparisons).
pub(super) fn pooled_ptr_of(r: AnyReg) -> Result<Reg<Ptr>, LowerError> {
    match r {
        AnyReg::Ptr(p) => Ok(p),
        AnyReg::Str(s) => Ok(Reg::new(s.id)),
        _ => Err(repr_mismatch("a pooled-handle operand position")),
    }
}

pub(super) fn any_of(r: AnyReg) -> Result<Reg<Any>, LowerError> {
    match r {
        AnyReg::Any(x) => Ok(x),
        _ => Err(repr_mismatch("a dynamic-cell operand position")),
    }
}

/// String repr normalization: a value whose static type is String always
/// carries the Str tag, whatever physical path produced the register —
/// cell reads, phis, and zero values all emit the pointer kind, so the
/// tag is re-derived from the type. Enforced at the variable-table choke
/// points (`declare_var`/`update_var` — every binding read is uniform)
/// and at the value-materialization points that bypass a binding
/// (`table_get`, inline-return phis); everywhere else the invariant
/// already holds.
pub(super) fn string_repr(ty: &Ty, reg: AnyReg) -> AnyReg {
    if ty == &Ty::Str {
        match reg {
            AnyReg::Ptr(p) => AnyReg::Str(Reg::new(p.id)),
            other => other,
        }
    } else {
        reg
    }
}

fn repr_mismatch(where_: &str) -> LowerError {
    LowerError(format!(
        "Lower Error: {where_} received a different repr — \
         the checker and the lowerer disagree"
    ))
}

pub(super) enum NumPair {
    II(Reg<Int>, Reg<Int>),
    FF(Reg<Float>, Reg<Float>),
}

pub(super) fn num_pair(l: AnyReg, r: AnyReg) -> Result<NumPair, LowerError> {
    match (l, r) {
        (AnyReg::Int(a), AnyReg::Int(b)) => Ok(NumPair::II(a, b)),
        (AnyReg::Float(a), AnyReg::Float(b)) => Ok(NumPair::FF(a, b)),
        _ => Err(repr_mismatch("arithmetic on")),
    }
}

pub(super) enum NumSingle {
    I(Reg<Int>),
    F(Reg<Float>),
}

pub(super) fn num_single(r: AnyReg) -> Result<NumSingle, LowerError> {
    match r {
        AnyReg::Int(a) => Ok(NumSingle::I(a)),
        AnyReg::Float(a) => Ok(NumSingle::F(a)),
        _ => Err(repr_mismatch("negation of")),
    }
}

pub(super) enum OrdPair {
    II(Reg<Int>, Reg<Int>),
    FF(Reg<Float>, Reg<Float>),
    BB(Reg<Bool>, Reg<Bool>),
    SS(Reg<crate::ir::Str>, Reg<crate::ir::Str>),
    PP(Reg<Ptr>, Reg<Ptr>),
    AA(Reg<crate::ir::Any>, Reg<crate::ir::Any>),
}

pub(super) fn ord_pair(l: AnyReg, r: AnyReg) -> Result<OrdPair, LowerError> {
    match (l, r) {
        (AnyReg::Int(a), AnyReg::Int(b)) => Ok(OrdPair::II(a, b)),
        (AnyReg::Float(a), AnyReg::Float(b)) => Ok(OrdPair::FF(a, b)),
        (AnyReg::Bool(a), AnyReg::Bool(b)) => Ok(OrdPair::BB(a, b)),
        (AnyReg::Str(a), AnyReg::Str(b)) => Ok(OrdPair::SS(a, b)),
        (AnyReg::Ptr(a), AnyReg::Ptr(b)) => Ok(OrdPair::PP(a, b)),
        (AnyReg::Any(a), AnyReg::Any(b)) => Ok(OrdPair::AA(a, b)),
        (AnyReg::Str(a), AnyReg::Ptr(b)) => Ok(OrdPair::PP(Reg::new(a.id), b)),
        (AnyReg::Ptr(a), AnyReg::Str(b)) => Ok(OrdPair::PP(a, Reg::new(b.id))),
        _ => Err(repr_mismatch("comparison of")),
    }
}

pub(super) fn phi_of(
    kind: RegKind,
    target: crate::ir::RegId,
    arms: Vec<(BlockId, AnyReg)>,
) -> Result<PhiRegs, LowerError> {
    fn narrow<K: PhiRepr>(
        target: crate::ir::RegId,
        arms: Vec<(BlockId, AnyReg)>,
    ) -> Result<PhiRegs, LowerError> {
        let mut typed = Vec::with_capacity(arms.len());
        for (block, reg) in arms {
            let reg = K::of(reg).ok_or_else(|| repr_mismatch("a join phi input position"))?;
            typed.push((block, reg));
        }
        Ok(K::phi(Reg::new(target), typed))
    }
    match kind {
        RegKind::Int => narrow::<Int>(target, arms),
        RegKind::Float => narrow::<Float>(target, arms),
        RegKind::Bool => narrow::<Bool>(target, arms),
        RegKind::Ptr => narrow::<Ptr>(target, arms),
        RegKind::Any => narrow::<crate::ir::Any>(target, arms),
    }
}

pub(super) fn phi_push(phi: &mut PhiRegs, block: BlockId, reg: AnyReg) -> Result<(), LowerError> {
    let mismatch = || repr_mismatch("a join phi input position");
    match phi {
        PhiRegs::Int { args, .. } => {
            args.push((block, <Int as PhiRepr>::of(reg).ok_or_else(mismatch)?))
        }
        PhiRegs::Float { args, .. } => {
            args.push((block, <Float as PhiRepr>::of(reg).ok_or_else(mismatch)?))
        }
        PhiRegs::Bool { args, .. } => {
            args.push((block, <Bool as PhiRepr>::of(reg).ok_or_else(mismatch)?))
        }
        PhiRegs::Ptr { args, .. } => {
            args.push((block, <Ptr as PhiRepr>::of(reg).ok_or_else(mismatch)?))
        }
        PhiRegs::Any { args, .. } => args.push((
            block,
            <crate::ir::Any as PhiRepr>::of(reg).ok_or_else(mismatch)?,
        )),
    }
    Ok(())
}

impl IrLowerer<'_> {
    pub(super) fn pack_any(&mut self, v: AnyReg) -> Result<AnyReg, LowerError> {
        if matches!(v, AnyReg::Any(_)) {
            return Ok(v);
        }
        let target = self.next_reg();
        let source = match v {
            AnyReg::Int(r) => PackRegs::Int(r),
            AnyReg::Float(r) => PackRegs::Float(r),
            AnyReg::Bool(r) => PackRegs::Bool(r),
            AnyReg::Str(r) => PackRegs::Str(r),
            AnyReg::Ptr(_) | AnyReg::Byte(_) => {
                return Err(LowerError(
                    "Lower Error: a dynamic cell holds scalars — a table value cannot be \
                     packed into one (the checker and the lowerer disagree)"
                        .into(),
                ));
            }
            AnyReg::Any(_) => unreachable!("the early return handled the Any repr"),
        };
        self.emit(Instruction::AnyPack {
            target: Reg::new(target),
            source,
        });
        Ok(AnyReg::Any(Reg::new(target)))
    }

    pub(super) fn num3<N: NumRepr>(
        &mut self,
        ctor: fn(NumRegs) -> Instruction,
        target: crate::ir::RegId,
        l: Reg<N>,
        r: Reg<N>,
    ) {
        self.emit(ctor(N::num3(Reg::new(target), l, r)));
    }

    pub(super) fn num3r<N: NumRepr>(
        &mut self,
        ctor: fn(NumRegsRhs) -> Instruction,
        target: crate::ir::RegId,
        l: Reg<N>,
        r: Reg<N>,
        rhs_const: Option<i64>,
    ) {
        self.emit(ctor(N::num3r(Reg::new(target), l, r, rhs_const)));
    }

    pub(super) fn neg1<N: NumRepr>(&mut self, target: crate::ir::RegId, source: Reg<N>) {
        self.emit(Instruction::Neg(N::num2(Reg::new(target), source)));
    }

    pub(super) fn cmp3<T: CmpRepr>(
        &mut self,
        ctor: fn(CmpRegs) -> Instruction,
        target: crate::ir::RegId,
        l: Reg<T>,
        r: Reg<T>,
    ) {
        self.emit(ctor(T::cmp(Reg::new(target), l, r)));
    }

    pub(super) fn emit_move_into(&mut self, target: crate::ir::RegId, source: AnyReg) -> AnyReg {
        let t = target;
        match source {
            AnyReg::Int(s) => {
                self.emit(Instruction::Move(MoveRegs::Int {
                    target: Reg::new(t),
                    source: s,
                }));
                AnyReg::Int(Reg::new(t))
            }
            AnyReg::Float(s) => {
                self.emit(Instruction::Move(MoveRegs::Float {
                    target: Reg::new(t),
                    source: s,
                }));
                AnyReg::Float(Reg::new(t))
            }
            AnyReg::Bool(s) => {
                self.emit(Instruction::Move(MoveRegs::Bool {
                    target: Reg::new(t),
                    source: s,
                }));
                AnyReg::Bool(Reg::new(t))
            }
            AnyReg::Str(s) => {
                self.emit(Instruction::Move(MoveRegs::Str {
                    target: Reg::new(t),
                    source: s,
                }));
                AnyReg::Str(Reg::new(t))
            }
            AnyReg::Ptr(s) => {
                self.emit(Instruction::Move(MoveRegs::Ptr {
                    target: Reg::new(t),
                    source: s,
                }));
                AnyReg::Ptr(Reg::new(t))
            }
            AnyReg::Byte(s) => {
                self.emit(Instruction::Move(MoveRegs::Byte {
                    target: Reg::new(t),
                    source: s,
                }));
                AnyReg::Byte(Reg::new(t))
            }
            AnyReg::Any(s) => {
                self.emit(Instruction::Move(MoveRegs::Any {
                    target: Reg::new(t),
                    source: s,
                }));
                AnyReg::Any(Reg::new(t))
            }
        }
    }

    pub(super) fn table_get(
        &mut self,
        target: crate::ir::RegId,
        table: Reg<Ptr>,
        index: TableKey,
        elem: &Ty,
    ) -> AnyReg {
        let out = match CellTy::of(elem) {
            CellTy::Int => self.get::<Int>(target, table, index),
            CellTy::Float => self.get::<Float>(target, table, index),
            CellTy::Bool => self.get::<Bool>(target, table, index),
            CellTy::Ptr => self.get::<Ptr>(target, table, index),
            CellTy::Byte => self.get::<Byte>(target, table, index),
            CellTy::Any => self.get::<crate::ir::Any>(target, table, index),
        };
        string_repr(elem, out)
    }

    fn get<E: CellRepr>(
        &mut self,
        target: crate::ir::RegId,
        table: Reg<Ptr>,
        index: TableKey,
    ) -> AnyReg {
        self.emit(Instruction::TableGet(E::get(
            Reg::new(target),
            table,
            index,
        )));
        E::any(Reg::new(target))
    }

    pub(super) fn table_set(
        &mut self,
        table: Reg<Ptr>,
        index: TableKey,
        value: AnyReg,
        elem: &Ty,
    ) -> Result<(), LowerError> {
        match value.into_cell() {
            CellVal::Int(v) => self.set(table, index, v, elem),
            CellVal::Float(v) => self.set(table, index, v, elem),
            CellVal::Bool(v) => self.set(table, index, v, elem),
            CellVal::Ptr(v) => self.set(table, index, v, elem),
            CellVal::Byte(v) => self.set(table, index, v, elem),
            CellVal::Any(v) => self.set(table, index, v, elem),
        }
    }

    pub(super) fn table_set_fast(
        &mut self,
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: AnyReg,
        elem: &Ty,
        layout: crate::shape::LayoutVerdict,
    ) -> Result<(), LowerError> {
        match value.into_cell() {
            CellVal::Int(v) => self.set_fast(table, index, v, elem, layout),
            CellVal::Float(v) => self.set_fast(table, index, v, elem, layout),
            CellVal::Bool(v) => self.set_fast(table, index, v, elem, layout),
            CellVal::Ptr(v) => self.set_fast(table, index, v, elem, layout),
            CellVal::Byte(v) => self.set_fast(table, index, v, elem, layout),
            CellVal::Any(v) => self.set_fast(table, index, v, elem, layout),
        }
    }

    fn set<E: CellRepr>(
        &mut self,
        table: Reg<Ptr>,
        index: TableKey,
        value: Reg<E>,
        elem: &Ty,
    ) -> Result<(), LowerError> {
        if CellTy::of(elem) != E::TAG {
            return Err(LowerError(
                "Lower Error: a stored value's repr disagrees with the table's element type — \
                 the checker and the lowerer disagree"
                    .into(),
            ));
        }
        self.emit(Instruction::TableSet(E::set(table, index, value)));
        Ok(())
    }

    fn set_fast<E: CellRepr>(
        &mut self,
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<E>,
        elem: &Ty,
        layout: crate::shape::LayoutVerdict,
    ) -> Result<(), LowerError> {
        if CellTy::of(elem) != E::TAG {
            return Err(LowerError(
                "Lower Error: a stored value's repr disagrees with the table's element type — \
                 the checker and the lowerer disagree"
                    .into(),
            ));
        }
        let cont = self.new_block();
        self.emit(Instruction::TableSetFast(E::set_fast(
            table, index, value, layout, cont,
        )));
        self.terminate(Terminator::Jump(cont));
        self.current_block = cont;
        Ok(())
    }

    pub(super) fn promote_to_float(
        &mut self,
        reg: AnyReg,
        ty: &Ty,
    ) -> Result<Reg<Float>, LowerError> {
        if matches!(ty, Ty::Int) {
            let source = int_of(reg)?;
            let target = self.next_reg();
            self.emit(Instruction::Sitofp {
                target: Reg::new(target),
                source,
            });
            Ok(Reg::new(target))
        } else {
            float_of(reg)
        }
    }
}
