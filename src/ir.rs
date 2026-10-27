use crate::shape::Ty;
use alm_rt::AlmElem;
use std::marker::PhantomData;

pub type BlockId = usize;

pub type RegId = u32;

#[derive(Debug, Clone, Copy)]
pub struct Int;
#[derive(Debug, Clone, Copy)]
pub struct Float;
#[derive(Debug, Clone, Copy)]
pub struct Bool;
#[derive(Debug, Clone, Copy)]
pub struct Str;
#[derive(Debug, Clone, Copy)]
pub struct Ptr;
#[derive(Debug, Clone, Copy)]
pub struct Byte;
#[derive(Debug, Clone, Copy)]
pub struct Any;
/// The register class of a table's string-key lane: an i64 that carries a
/// negative interned identity (STR_KEY_TAG | fnv1a_62, async/str_pool.c).
/// Phantom-typed so ONLY the two key-derivation instructions
/// (`StrKeyConst` for folded literals, `StrKey` for dynamic handles) can
/// produce one — a user integer, however produced at runtime, can never
/// address a record cell because it never shares a register class with
/// `Reg<StrKey>` and the backend routes the two to distinct runtime
/// entry points (`alm_tbl_set_skey` vs `alm_tbl_set`).
#[derive(Debug, Clone, Copy)]
pub struct StrKey;

#[derive(Debug, Clone, Copy)]
pub struct Reg<R: Repr + ?Sized> {
    pub id: RegId,
    _repr: PhantomData<R>,
}

impl<R: Repr> Reg<R> {
    pub fn new(id: RegId) -> Self {
        Self {
            id,
            _repr: PhantomData,
        }
    }
}

pub trait Repr {
    fn llvm() -> &'static str;
    fn storage() -> &'static str {
        Self::llvm()
    }
    fn esize() -> u32 {
        8
    }
    const IS_PACKED: bool = false;
    const IS_FLOAT: bool = false;
    const REG_FACE: bool = false;
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String);
    fn any(reg: Reg<Self>) -> AnyReg;
}

impl Repr for Int {
    fn llvm() -> &'static str {
        "i64"
    }
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String) {
        code.push_str(&format!("  %v{} = add i64 %v{}, 0\n", target.id, source.id));
    }
    fn any(reg: Reg<Self>) -> AnyReg {
        AnyReg::Int(reg)
    }
}

impl Repr for StrKey {
    fn llvm() -> &'static str {
        "i64"
    }
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String) {
        code.push_str(&format!("  %v{} = add i64 %v{}, 0\n", target.id, source.id));
    }
    // unreachable in practice: keys are addressing lanes, never packed
    // into Any cells — the impl exists only because Reg<R: Repr> demands it
    fn any(reg: Reg<Self>) -> AnyReg {
        AnyReg::Int(Reg::new(reg.id))
    }
}

impl Repr for Float {
    fn llvm() -> &'static str {
        "double"
    }
    const IS_FLOAT: bool = true;
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String) {
        code.push_str(&format!(
            "  %v{} = fadd double %v{}, 0.0\n",
            target.id, source.id
        ));
    }
    fn any(reg: Reg<Self>) -> AnyReg {
        AnyReg::Float(reg)
    }
}

impl Repr for Bool {
    fn llvm() -> &'static str {
        "i1"
    }
    fn storage() -> &'static str {
        "i8"
    }
    fn esize() -> u32 {
        1
    }
    const IS_PACKED: bool = true;
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String) {
        code.push_str(&format!("  %v{} = or i1 %v{}, 0\n", target.id, source.id));
    }
    fn any(reg: Reg<Self>) -> AnyReg {
        AnyReg::Bool(reg)
    }
}

impl Repr for Str {
    fn llvm() -> &'static str {
        "ptr"
    }
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String) {
        code.push_str(&format!(
            "  %v{} = getelementptr i8, ptr %v{}, i64 0\n",
            target.id, source.id
        ));
    }
    fn any(reg: Reg<Self>) -> AnyReg {
        AnyReg::Str(reg)
    }
}

impl Repr for Ptr {
    fn llvm() -> &'static str {
        "ptr"
    }
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String) {
        code.push_str(&format!(
            "  %v{} = getelementptr i8, ptr %v{}, i64 0\n",
            target.id, source.id
        ));
    }
    fn any(reg: Reg<Self>) -> AnyReg {
        AnyReg::Ptr(reg)
    }
}

impl Repr for Byte {
    fn llvm() -> &'static str {
        "i8"
    }
    fn esize() -> u32 {
        1
    }
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String) {
        code.push_str(&format!("  %v{} = or i8 %v{}, 0\n", target.id, source.id));
    }
    fn any(reg: Reg<Self>) -> AnyReg {
        AnyReg::Byte(reg)
    }
}

impl Repr for Any {
    fn llvm() -> &'static str {
        "i128"
    }
    fn esize() -> u32 {
        16
    }
    const REG_FACE: bool = true;
    fn emit_move(target: &Reg<Self>, source: &Reg<Self>, code: &mut String) {
        code.push_str(&format!(
            "  %v{} = add i128 %v{}, 0\n",
            target.id, source.id
        ));
    }
    fn any(reg: Reg<Self>) -> AnyReg {
        AnyReg::Any(reg)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum AnyReg {
    Int(Reg<Int>),
    Float(Reg<Float>),
    Bool(Reg<Bool>),
    Str(Reg<Str>),
    Ptr(Reg<Ptr>),
    Byte(Reg<Byte>),
    Any(Reg<Any>),
}

impl AnyReg {
    pub fn kind(&self) -> RegKind {
        match self {
            AnyReg::Int(_) => RegKind::Int,
            AnyReg::Float(_) => RegKind::Float,
            AnyReg::Bool(_) => RegKind::Bool,
            AnyReg::Str(_) | AnyReg::Ptr(_) | AnyReg::Byte(_) => RegKind::Ptr,
            AnyReg::Any(_) => RegKind::Any,
        }
    }

    pub fn id(&self) -> RegId {
        match self {
            AnyReg::Int(r) => r.id,
            AnyReg::Float(r) => r.id,
            AnyReg::Bool(r) => r.id,
            AnyReg::Str(r) => r.id,
            AnyReg::Ptr(r) => r.id,
            AnyReg::Byte(r) => r.id,
            AnyReg::Any(r) => r.id,
        }
    }

    pub fn into_cell(self) -> CellVal {
        match self {
            AnyReg::Int(r) => CellVal::Int(r),
            AnyReg::Float(r) => CellVal::Float(r),
            AnyReg::Bool(r) => CellVal::Bool(r),
            AnyReg::Str(r) => CellVal::Ptr(Reg::new(r.id)),
            AnyReg::Ptr(r) => CellVal::Ptr(r),
            AnyReg::Byte(r) => CellVal::Byte(r),
            AnyReg::Any(r) => CellVal::Any(r),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegKind {
    Int,
    Float,
    Bool,
    Ptr,
    Any,
}

impl RegKind {
    pub fn reg(self, id: RegId) -> AnyReg {
        match self {
            RegKind::Int => AnyReg::Int(Reg::new(id)),
            RegKind::Float => AnyReg::Float(Reg::new(id)),
            RegKind::Bool => AnyReg::Bool(Reg::new(id)),
            RegKind::Ptr => AnyReg::Ptr(Reg::new(id)),
            RegKind::Any => AnyReg::Any(Reg::new(id)),
        }
    }
}

pub fn repr_of(ty: &Ty) -> RegKind {
    match ty {
        Ty::Int => RegKind::Int,
        Ty::Flt => RegKind::Float,
        Ty::Bool => RegKind::Bool,
        Ty::Any => RegKind::Any,
        Ty::Str | Ty::Tbl(_) | Ty::Unknown(_) => RegKind::Ptr,
        Ty::Ffi | Ty::FfiLib | Ty::Coro => RegKind::Ptr,
        Ty::Closure(_) => RegKind::Ptr,
        // the artifact path sees only decided kinds and unknowns — the
        // elem table materializes flow state before facts assemble
        Ty::Pending | Ty::Conflict => unreachable!("flow state never rides the artifact path"),
    }
}

#[derive(Debug, Clone, Copy)]
pub enum CellVal {
    Int(Reg<Int>),
    Float(Reg<Float>),
    Bool(Reg<Bool>),
    Ptr(Reg<Ptr>),
    Byte(Reg<Byte>),
    Any(Reg<Any>),
}

#[derive(Debug, Clone, Copy)]
pub enum PackRegs {
    Int(Reg<Int>),
    Float(Reg<Float>),
    Bool(Reg<Bool>),
    Str(Reg<Str>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CellTy {
    Int,
    Float,
    Bool,
    Ptr,
    Byte,
    Any,
}

impl CellTy {
    pub fn of(ty: &Ty) -> Self {
        match ty {
            Ty::Int => CellTy::Int,
            Ty::Flt => CellTy::Float,
            Ty::Bool => CellTy::Bool,
            Ty::Any => CellTy::Any,
            Ty::Str | Ty::Tbl(_) => CellTy::Ptr,
            Ty::Ffi | Ty::FfiLib | Ty::Coro | Ty::Unknown(_) => CellTy::Byte,
            Ty::Closure(_) => CellTy::Ptr,
            Ty::Pending | Ty::Conflict => unreachable!("flow state never rides the artifact path"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum MoveRegs {
    Int {
        target: Reg<Int>,
        source: Reg<Int>,
    },
    Float {
        target: Reg<Float>,
        source: Reg<Float>,
    },
    Bool {
        target: Reg<Bool>,
        source: Reg<Bool>,
    },
    Str {
        target: Reg<Str>,
        source: Reg<Str>,
    },
    Ptr {
        target: Reg<Ptr>,
        source: Reg<Ptr>,
    },
    Byte {
        target: Reg<Byte>,
        source: Reg<Byte>,
    },
    Any {
        target: Reg<Any>,
        source: Reg<Any>,
    },
}

/// The addressing lane of one table access: a user Integer index, or a
/// string-key lane produced only by the key derivations. Constructed
/// solely by the lowerer's `lower_index_key` — the two register classes
/// cannot be confused, and the backend picks the runtime entry point
/// (int vs skey) from this tag.
#[derive(Debug, Clone, Copy)]
pub enum TableKey {
    Int(Reg<Int>),
    Str(Reg<StrKey>),
}

impl TableKey {
    pub fn id(&self) -> RegId {
        match self {
            TableKey::Int(r) => r.id,
            TableKey::Str(r) => r.id,
        }
    }
}

#[derive(Debug, Clone)]
pub enum CellGet {
    Int {
        target: Reg<Int>,
        table: Reg<Ptr>,
        index: TableKey,
    },
    Float {
        target: Reg<Float>,
        table: Reg<Ptr>,
        index: TableKey,
    },
    Bool {
        target: Reg<Bool>,
        table: Reg<Ptr>,
        index: TableKey,
    },
    Ptr {
        target: Reg<Ptr>,
        table: Reg<Ptr>,
        index: TableKey,
    },
    Byte {
        target: Reg<Byte>,
        table: Reg<Ptr>,
        index: TableKey,
    },
    Any {
        target: Reg<Any>,
        table: Reg<Ptr>,
        index: TableKey,
    },
}

#[derive(Debug, Clone)]
pub enum CellSet {
    Int {
        table: Reg<Ptr>,
        index: TableKey,
        value: Reg<Int>,
    },
    Float {
        table: Reg<Ptr>,
        index: TableKey,
        value: Reg<Float>,
    },
    Bool {
        table: Reg<Ptr>,
        index: TableKey,
        value: Reg<Bool>,
    },
    Ptr {
        table: Reg<Ptr>,
        index: TableKey,
        value: Reg<Ptr>,
    },
    Byte {
        table: Reg<Ptr>,
        index: TableKey,
        value: Reg<Byte>,
    },
    Any {
        table: Reg<Ptr>,
        index: TableKey,
        value: Reg<Any>,
    },
}

#[derive(Debug, Clone)]
pub enum CellSetFast {
    Int {
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Int>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    },
    Float {
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Float>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    },
    Bool {
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Bool>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    },
    Ptr {
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Ptr>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    },
    Byte {
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Byte>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    },
    Any {
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Any>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    },
}

impl CellSetFast {
    pub fn cont(&self) -> BlockId {
        match self {
            CellSetFast::Int { cont, .. }
            | CellSetFast::Float { cont, .. }
            | CellSetFast::Bool { cont, .. }
            | CellSetFast::Ptr { cont, .. }
            | CellSetFast::Byte { cont, .. }
            | CellSetFast::Any { cont, .. } => *cont,
        }
    }
}

#[derive(Debug, Clone)]
pub enum NumRegs {
    Int {
        target: Reg<Int>,
        left: Reg<Int>,
        right: Reg<Int>,
    },
    Float {
        target: Reg<Float>,
        left: Reg<Float>,
        right: Reg<Float>,
    },
}

#[derive(Debug, Clone)]
pub enum NumRegsRhs {
    Int {
        target: Reg<Int>,
        left: Reg<Int>,
        right: Reg<Int>,
        rhs_const: Option<i64>,
    },
    Float {
        target: Reg<Float>,
        left: Reg<Float>,
        right: Reg<Float>,
        rhs_const: Option<i64>,
    },
}

#[derive(Debug, Clone)]
pub enum UnaryNum {
    Int {
        target: Reg<Int>,
        source: Reg<Int>,
    },
    Float {
        target: Reg<Float>,
        source: Reg<Float>,
    },
}

#[derive(Debug, Clone)]
pub enum CmpRegs {
    Int {
        target: Reg<Bool>,
        left: Reg<Int>,
        right: Reg<Int>,
    },
    Float {
        target: Reg<Bool>,
        left: Reg<Float>,
        right: Reg<Float>,
    },
    Bool {
        target: Reg<Bool>,
        left: Reg<Bool>,
        right: Reg<Bool>,
    },
    Str {
        target: Reg<Bool>,
        left: Reg<Str>,
        right: Reg<Str>,
    },
    Ptr {
        target: Reg<Bool>,
        left: Reg<Ptr>,
        right: Reg<Ptr>,
    },
    Any {
        target: Reg<Bool>,
        left: Reg<Any>,
        right: Reg<Any>,
    },
}

#[derive(Debug, Clone)]
pub enum PhiRegs {
    Int {
        target: Reg<Int>,
        args: Vec<(BlockId, Reg<Int>)>,
    },
    Float {
        target: Reg<Float>,
        args: Vec<(BlockId, Reg<Float>)>,
    },
    Bool {
        target: Reg<Bool>,
        args: Vec<(BlockId, Reg<Bool>)>,
    },
    Ptr {
        target: Reg<Ptr>,
        args: Vec<(BlockId, Reg<Ptr>)>,
    },
    Any {
        target: Reg<Any>,
        args: Vec<(BlockId, Reg<Any>)>,
    },
}

impl PhiRegs {
    pub fn target_id(&self) -> RegId {
        match self {
            PhiRegs::Int { target, .. } => target.id,
            PhiRegs::Float { target, .. } => target.id,
            PhiRegs::Bool { target, .. } => target.id,
            PhiRegs::Ptr { target, .. } => target.id,
            PhiRegs::Any { target, .. } => target.id,
        }
    }

    pub fn arg_blocks(&self) -> Vec<BlockId> {
        fn blocks<R: Repr>(args: &[(BlockId, Reg<R>)]) -> Vec<BlockId> {
            args.iter().map(|(b, _)| *b).collect()
        }
        match self {
            PhiRegs::Int { args, .. } => blocks(args),
            PhiRegs::Float { args, .. } => blocks(args),
            PhiRegs::Bool { args, .. } => blocks(args),
            PhiRegs::Ptr { args, .. } => blocks(args),
            PhiRegs::Any { args, .. } => blocks(args),
        }
    }
}

pub trait NumRepr: Repr {
    fn num3(target: Reg<Self>, left: Reg<Self>, right: Reg<Self>) -> NumRegs;
    fn num3r(
        target: Reg<Self>,
        left: Reg<Self>,
        right: Reg<Self>,
        rhs_const: Option<i64>,
    ) -> NumRegsRhs;
    fn num2(target: Reg<Self>, source: Reg<Self>) -> UnaryNum;
}

impl NumRepr for Int {
    fn num3(target: Reg<Self>, left: Reg<Self>, right: Reg<Self>) -> NumRegs {
        NumRegs::Int {
            target,
            left,
            right,
        }
    }
    fn num3r(
        target: Reg<Self>,
        left: Reg<Self>,
        right: Reg<Self>,
        rhs_const: Option<i64>,
    ) -> NumRegsRhs {
        NumRegsRhs::Int {
            target,
            left,
            right,
            rhs_const,
        }
    }
    fn num2(target: Reg<Self>, source: Reg<Self>) -> UnaryNum {
        UnaryNum::Int { target, source }
    }
}

impl NumRepr for Float {
    fn num3(target: Reg<Self>, left: Reg<Self>, right: Reg<Self>) -> NumRegs {
        NumRegs::Float {
            target,
            left,
            right,
        }
    }
    fn num3r(
        target: Reg<Self>,
        left: Reg<Self>,
        right: Reg<Self>,
        rhs_const: Option<i64>,
    ) -> NumRegsRhs {
        NumRegsRhs::Float {
            target,
            left,
            right,
            rhs_const,
        }
    }
    fn num2(target: Reg<Self>, source: Reg<Self>) -> UnaryNum {
        UnaryNum::Float { target, source }
    }
}

pub trait CellRepr: Repr {
    const TAG: CellTy;
    fn get(target: Reg<Self>, table: Reg<Ptr>, index: TableKey) -> CellGet;
    fn set(table: Reg<Ptr>, index: TableKey, value: Reg<Self>) -> CellSet;
    fn set_fast(
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Self>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    ) -> CellSetFast;
}

impl CellRepr for Int {
    const TAG: CellTy = CellTy::Int;
    fn get(target: Reg<Self>, table: Reg<Ptr>, index: TableKey) -> CellGet {
        CellGet::Int {
            target,
            table,
            index,
        }
    }
    fn set(table: Reg<Ptr>, index: TableKey, value: Reg<Self>) -> CellSet {
        CellSet::Int {
            table,
            index,
            value,
        }
    }
    fn set_fast(
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Self>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    ) -> CellSetFast {
        CellSetFast::Int {
            table,
            index,
            value,
            layout,
            cont,
        }
    }
}

impl CellRepr for Float {
    const TAG: CellTy = CellTy::Float;
    fn get(target: Reg<Self>, table: Reg<Ptr>, index: TableKey) -> CellGet {
        CellGet::Float {
            target,
            table,
            index,
        }
    }
    fn set(table: Reg<Ptr>, index: TableKey, value: Reg<Self>) -> CellSet {
        CellSet::Float {
            table,
            index,
            value,
        }
    }
    fn set_fast(
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Self>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    ) -> CellSetFast {
        CellSetFast::Float {
            table,
            index,
            value,
            layout,
            cont,
        }
    }
}

impl CellRepr for Bool {
    const TAG: CellTy = CellTy::Bool;
    fn get(target: Reg<Self>, table: Reg<Ptr>, index: TableKey) -> CellGet {
        CellGet::Bool {
            target,
            table,
            index,
        }
    }
    fn set(table: Reg<Ptr>, index: TableKey, value: Reg<Self>) -> CellSet {
        CellSet::Bool {
            table,
            index,
            value,
        }
    }
    fn set_fast(
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Self>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    ) -> CellSetFast {
        CellSetFast::Bool {
            table,
            index,
            value,
            layout,
            cont,
        }
    }
}

impl CellRepr for Ptr {
    const TAG: CellTy = CellTy::Ptr;
    fn get(target: Reg<Self>, table: Reg<Ptr>, index: TableKey) -> CellGet {
        CellGet::Ptr {
            target,
            table,
            index,
        }
    }
    fn set(table: Reg<Ptr>, index: TableKey, value: Reg<Self>) -> CellSet {
        CellSet::Ptr {
            table,
            index,
            value,
        }
    }
    fn set_fast(
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Self>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    ) -> CellSetFast {
        CellSetFast::Ptr {
            table,
            index,
            value,
            layout,
            cont,
        }
    }
}

impl CellRepr for Byte {
    const TAG: CellTy = CellTy::Byte;
    fn get(target: Reg<Self>, table: Reg<Ptr>, index: TableKey) -> CellGet {
        CellGet::Byte {
            target,
            table,
            index,
        }
    }
    fn set(table: Reg<Ptr>, index: TableKey, value: Reg<Self>) -> CellSet {
        CellSet::Byte {
            table,
            index,
            value,
        }
    }
    fn set_fast(
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Self>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    ) -> CellSetFast {
        CellSetFast::Byte {
            table,
            index,
            value,
            layout,
            cont,
        }
    }
}

impl CellRepr for Any {
    const TAG: CellTy = CellTy::Any;
    fn get(target: Reg<Self>, table: Reg<Ptr>, index: TableKey) -> CellGet {
        CellGet::Any {
            target,
            table,
            index,
        }
    }
    fn set(table: Reg<Ptr>, index: TableKey, value: Reg<Self>) -> CellSet {
        CellSet::Any {
            table,
            index,
            value,
        }
    }
    fn set_fast(
        table: Reg<Ptr>,
        index: Reg<Int>,
        value: Reg<Self>,
        layout: crate::shape::LayoutVerdict,
        cont: BlockId,
    ) -> CellSetFast {
        CellSetFast::Any {
            table,
            index,
            value,
            layout,
            cont,
        }
    }
}

pub trait CmpRepr: Repr {
    fn cmp(target: Reg<Bool>, left: Reg<Self>, right: Reg<Self>) -> CmpRegs;
}

impl CmpRepr for Int {
    fn cmp(target: Reg<Bool>, left: Reg<Self>, right: Reg<Self>) -> CmpRegs {
        CmpRegs::Int {
            target,
            left,
            right,
        }
    }
}

impl CmpRepr for Float {
    fn cmp(target: Reg<Bool>, left: Reg<Self>, right: Reg<Self>) -> CmpRegs {
        CmpRegs::Float {
            target,
            left,
            right,
        }
    }
}

impl CmpRepr for Bool {
    fn cmp(target: Reg<Bool>, left: Reg<Self>, right: Reg<Self>) -> CmpRegs {
        CmpRegs::Bool {
            target,
            left,
            right,
        }
    }
}

impl CmpRepr for Str {
    fn cmp(target: Reg<Bool>, left: Reg<Self>, right: Reg<Self>) -> CmpRegs {
        CmpRegs::Str {
            target,
            left,
            right,
        }
    }
}

impl CmpRepr for Ptr {
    fn cmp(target: Reg<Bool>, left: Reg<Self>, right: Reg<Self>) -> CmpRegs {
        CmpRegs::Ptr {
            target,
            left,
            right,
        }
    }
}

impl CmpRepr for Any {
    fn cmp(target: Reg<Bool>, left: Reg<Self>, right: Reg<Self>) -> CmpRegs {
        CmpRegs::Any {
            target,
            left,
            right,
        }
    }
}

pub trait PhiRepr: Repr {
    fn phi(target: Reg<Self>, args: Vec<(BlockId, Reg<Self>)>) -> PhiRegs;
    fn of(reg: AnyReg) -> Option<Reg<Self>>;
}

impl PhiRepr for Int {
    fn phi(target: Reg<Self>, args: Vec<(BlockId, Reg<Self>)>) -> PhiRegs {
        PhiRegs::Int { target, args }
    }
    fn of(reg: AnyReg) -> Option<Reg<Self>> {
        match reg {
            AnyReg::Int(r) => Some(r),
            _ => None,
        }
    }
}

impl PhiRepr for Float {
    fn phi(target: Reg<Self>, args: Vec<(BlockId, Reg<Self>)>) -> PhiRegs {
        PhiRegs::Float { target, args }
    }
    fn of(reg: AnyReg) -> Option<Reg<Self>> {
        match reg {
            AnyReg::Float(r) => Some(r),
            _ => None,
        }
    }
}

impl PhiRepr for Bool {
    fn phi(target: Reg<Self>, args: Vec<(BlockId, Reg<Self>)>) -> PhiRegs {
        PhiRegs::Bool { target, args }
    }
    fn of(reg: AnyReg) -> Option<Reg<Self>> {
        match reg {
            AnyReg::Bool(r) => Some(r),
            _ => None,
        }
    }
}

impl PhiRepr for Ptr {
    fn phi(target: Reg<Self>, args: Vec<(BlockId, Reg<Self>)>) -> PhiRegs {
        PhiRegs::Ptr { target, args }
    }
    fn of(reg: AnyReg) -> Option<Reg<Self>> {
        match reg {
            AnyReg::Ptr(r) => Some(r),
            AnyReg::Str(r) => Some(Reg::new(r.id)),
            _ => None,
        }
    }
}

impl PhiRepr for Any {
    fn phi(target: Reg<Self>, args: Vec<(BlockId, Reg<Self>)>) -> PhiRegs {
        PhiRegs::Any { target, args }
    }
    fn of(reg: AnyReg) -> Option<Reg<Self>> {
        match reg {
            AnyReg::Any(r) => Some(r),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Terminator {
    Jump(BlockId),
    Branch {
        cond: Reg<Bool>,
        true_block: BlockId,
        false_block: BlockId,
    },
    Halt,
    Return(Reg<Ptr>),
}

#[derive(Debug, Clone)]
pub enum Instruction {
    LoadInt {
        target: Reg<Int>,
        val: i64,
    },
    /// alm_str_key: the negative table key of a pooled string — one
    /// unaligned load of the 8-byte prefix off the canonical handle
    /// (async/str_pool.c). The ONLY runtime derivation of a StrKey
    /// register; the constant-fold twin is StrKeyConst.
    StrKey {
        target: Reg<StrKey>,
        s: Reg<Str>,
    },
    /// The compile-time fold of a literal string key: STR_KEY_TAG |
    /// fnv1a_62 of the bytes, baked as an i64 constant (rt's
    /// str_key_of_bytes — the ABI twin of str_pool.c's derive). The ONLY
    /// constant producer of a StrKey register.
    StrKeyConst {
        target: Reg<StrKey>,
        val: i64,
    },
    LoadFloat {
        target: Reg<Float>,
        val: f64,
    },
    LoadBool {
        target: Reg<Bool>,
        val: bool,
    },
    LoadAnyZero {
        target: Reg<Any>,
    },
    LoadString {
        target: Reg<Str>,
        val: String,
    },
    StrLen {
        target: Reg<Int>,
        s: Reg<Str>,
    },
    AnyLen {
        target: Reg<Int>,
        source: Reg<Any>,
    },
    TableLen {
        target: Reg<Int>,
        table: Reg<Ptr>,
    },
    AnyPack {
        target: Reg<Any>,
        source: PackRegs,
    },
    LoadNull {
        target: Reg<Ptr>,
    },
    BindArgs {
        target: Reg<Ptr>,
    },
    Move(MoveRegs),

    TableNew {
        target: Reg<Ptr>,
        elem: Ty,
        flags: u8,
    },
    TableGet(CellGet),
    TableReserve {
        table: Reg<Ptr>,
        bound: Reg<Int>,
    },
    TableSetFast(CellSetFast),
    TableSet(CellSet),
    TableFree {
        table: Reg<Ptr>,
    },
    TableFreeExcept {
        table: Reg<Ptr>,
        keeps: Vec<Reg<Ptr>>,
    },

    SysAllocCount {
        target: Reg<Int>,
    },

    SysExecCount {
        target: Reg<Int>,
    },

    CoroCreate {
        target: Reg<Int>,
        lib: Reg<Ptr>,
    },
    CoroResume {
        target: Reg<Int>,
        handle: Reg<Int>,
        args: Reg<Ptr>,
    },
    CoroYield {
        target: Reg<Int>,
        value: Reg<Int>,
    },
    CoroStatus {
        target: Reg<Str>,
        handle: Reg<Int>,
    },
    CoroClose {
        target: Reg<Int>,
        handle: Reg<Int>,
    },

    FfiLoad {
        target: Reg<Ptr>,
        path: Reg<Ptr>,
    },
    FfiArgKind {
        target: Reg<Int>,
        lib: Reg<Ptr>,
    },
    FfiCall {
        lib: Reg<Ptr>,
        sym: String,
        arg: Reg<Ptr>,
    },

    Add(NumRegs),
    Sub(NumRegs),
    Mul(NumRegs),
    Sitofp {
        target: Reg<Float>,
        source: Reg<Int>,
    },
    Div {
        target: Reg<Float>,
        left: Reg<Float>,
        right: Reg<Float>,
    },
    IntDiv(NumRegsRhs),
    Mod(NumRegsRhs),
    Neg(UnaryNum),
    Less(CmpRegs),
    Leq(CmpRegs),
    Geq(CmpRegs),
    Eq(CmpRegs),
    Not {
        target: Reg<Bool>,
        source: Reg<Bool>,
    },

    Phi(PhiRegs),

    Print {
        operands: Vec<(RegId, Ty)>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceLoc {
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone)]
pub struct DbgBind {
    pub after: usize,
    pub name: String,
    pub reg: RegId,
    pub kind: RegKind,
    pub loc: Option<SourceLoc>,
    pub param: Option<u32>,
}

#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub id: BlockId,
    pub instrs: Vec<Instruction>,
    pub locs: Vec<Option<SourceLoc>>,
    pub terminator: Option<Terminator>,
    pub term_loc: Option<SourceLoc>,
    pub dbg_values: Vec<DbgBind>,
}

impl BasicBlock {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            instrs: Vec::new(),
            locs: Vec::new(),
            terminator: None,
            term_loc: None,
            dbg_values: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct IrProgram {
    pub blocks: Vec<BasicBlock>,
    pub boundary_elem: Option<AlmElem>,
    pub entry: EntryKind,
    pub source_file: std::path::PathBuf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum EntryKind {
    #[default]
    Lib,
    Exe {
        args: bool,
    },
}
