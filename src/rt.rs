#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{Layout, alloc_zeroed, dealloc, realloc};
use std::collections::HashMap;
use std::ffi::c_void;
use std::ptr;
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicUsize, Ordering};

use crate::trace::{
    TRACE_CORO_CLOSE, TRACE_CORO_DEAD, TRACE_CORO_RESUME, TRACE_CORO_SPAWN, TRACE_CORO_YIELD,
    TRACE_CORO_YIELD_DROPPED, TRACE_FAIL_ANY_LEN, TRACE_FAIL_CORO_CREATE, TRACE_FAIL_DIV_ZERO,
    TRACE_FAIL_FFI_LOAD, TRACE_FAIL_FFI_SYM, TRACE_FAIL_LEAK_DETECTED, TRACE_FAIL_NULL_ROW_STORE,
    TRACE_RT_ALLOC, TRACE_RT_FFI_LOAD, TRACE_RT_FREE, TRACE_RT_FREE_CHILD, TRACE_RT_GROW_NULL,
    TRACE_RT_RESERVE_NULL,
};

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TableMode {
    Dense = 0,
    Sparse = 1,
}

/// #[repr(C)] header. Field layout (offset: type), ABI-pinned by the
#[repr(C)]
pub struct AlmTable {
    pub data: *mut u8,
    pub len: i64,
    pub reserve: usize,
    pub esize: usize,
    pub mode: TableMode,
    pub contains_tables: u8,
    pub elem_kind: u8,
    pub sparse_map: *mut HashMap<i64, u128>,
    pub border: i64,
}

const _: () = {
    use std::mem::{offset_of, size_of};
    assert!(
        size_of::<AlmTable>() == 56,
        "AlmTable must stay the 56-byte ABI"
    );
    assert!(offset_of!(AlmTable, data) == 0);
    assert!(offset_of!(AlmTable, len) == 8);
    assert!(offset_of!(AlmTable, reserve) == 16);
    assert!(offset_of!(AlmTable, esize) == 24);
    assert!(offset_of!(AlmTable, mode) == 32);
    assert!(offset_of!(AlmTable, contains_tables) == 33);
    assert!(offset_of!(AlmTable, elem_kind) == 34);
    assert!(offset_of!(AlmTable, sparse_map) == 40);
    assert!(offset_of!(AlmTable, border) == 48);
};

static ALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);
static TOTAL_COUNT: AtomicUsize = AtomicUsize::new(0);

// --- exec tenancy: this copy's handle into the shared C11 substrate -----
//
// Every process-wide alm concern (the trace plate file, the exit-time leak
// report, cross-instance visibility) lives in libalm_async.so — one copy
// per process, loader-guaranteed. alm_rt keeps only its exec_id handle and
// the fast local counters it mirrors into its ExecSlot.

const EXEC_UNREGISTERED: i32 = -2;
const EXEC_REGISTERING: i32 = -3;
static EXEC_ID: AtomicI32 = AtomicI32::new(EXEC_UNREGISTERED);
static IS_EXE: AtomicBool = AtomicBool::new(false);
static LOCAL_LEAK_HOOK: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

// set by the unified exit report in the .so; kept for the registry-full
// fallback path, where this copy owes its own leak check
unsafe extern "C" {
    fn vx_trace_poke_exec(exec_id: i32, slot: u8);
    fn vx_str_intern(s: *const u8, len: usize) -> *const u8;
    fn vx_str_register(strtab: *mut *const u8, n: usize);
    fn vx_exec_register(name: *const i8, flags: u32) -> i32;
    fn vx_exec_census_set(id: i32, live: i64, total: i64);
    fn vx_exec_state_set(id: i32, state: u32);
    fn vx_exec_count() -> i32;
    fn vx_coro_create(lib: *mut c_void) -> i32;
    fn vx_coro_send(id: i32, a: u64, b: u64, c: u64);
    fn vx_coro_start(id: i32) -> i32;
    fn vx_coro_pull(id: i32) -> i64;
    fn vx_coro_yield(value: u64) -> i64;
    fn vx_coro_status(id: i32) -> u32;
    fn vx_coro_join(id: i32);
    fn dladdr(addr: *const c_void, info: *mut DlInfo) -> i32;
}

#[repr(C)]
struct DlInfo {
    dli_fname: *const i8,
    dli_fbase: *mut c_void,
    dli_sname: *const i8,
    dli_saddr: *mut c_void,
}

// lives in this copy's .data: dladdr on its address names the artifact
// (exe or .so) this alm_rt copy was linked into
static MODULE_MARK: u8 = 0;

/// The exec_id this copy registered under (single-flight; -1 if the
/// registry is full). Registering names the module via dladdr and hands
/// the shared substrate the census it will report at process exit.
fn exec_id() -> i32 {
    match EXEC_ID.load(Ordering::Relaxed) {
        id if id != EXEC_UNREGISTERED => id,
        _ => {
            if EXEC_ID
                .compare_exchange(
                    EXEC_UNREGISTERED,
                    EXEC_REGISTERING,
                    Ordering::Relaxed,
                    Ordering::Relaxed,
                )
                .is_err()
            {
                while EXEC_ID.load(Ordering::Relaxed) == EXEC_REGISTERING {
                    std::hint::spin_loop();
                }
                return EXEC_ID.load(Ordering::Relaxed);
            }
            let id = unsafe { register_now() };
            EXEC_ID.store(id, Ordering::Relaxed);
            id
        }
    }
}

unsafe fn register_now() -> i32 {
    let mut info: DlInfo = std::mem::zeroed();
    let name: Vec<u8> = if unsafe { dladdr(ptr::addr_of!(MODULE_MARK).cast::<c_void>(), &mut info) }
        != 0
        && !info.dli_fname.is_null()
    {
        let full = unsafe { cstr_bytes(info.dli_fname.cast()) };
        match full.iter().rposition(|&b| b == b'/') {
            Some(at) => full[at + 1..].to_vec(),
            None => full.to_vec(),
        }
    } else {
        b"alm".to_vec()
    };
    let mut nul = name;
    nul.push(0);
    // VX_EXEC_F_EXE (0x1) when alm_exec_main ran first, else VX_EXEC_F_SO (0x2)
    let flags: u32 = if IS_EXE.load(Ordering::Relaxed) {
        0x1
    } else {
        0x2
    };
    unsafe { vx_exec_register(nul.as_ptr().cast(), flags) }
}

/// Sticky trace byte on the process-wide plate — the single C11 shared
/// object owns the file; pokes from every alm_rt copy and foreign C
/// companions land on the same MAP_SHARED inode.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_trace_set(slot: u8) {
    // a raw load, not exec_id(): a poke never forces registration (out-of-
    // range ids ride the anonymous 0xFF event tag in the substrate)
    unsafe { vx_trace_poke_exec(EXEC_ID.load(Ordering::Relaxed), slot) };
}

unsafe fn mirror_census(id: i32) {
    if id >= 0 {
        unsafe {
            vx_exec_census_set(
                id,
                ALLOC_COUNT.load(Ordering::Relaxed) as i64,
                TOTAL_COUNT.load(Ordering::Relaxed) as i64,
            )
        };
    }
}

unsafe extern "C" fn alm_trace_leak_check() {
    if ALLOC_COUNT.load(Ordering::Relaxed) > 0 {
        unsafe { alm_trace_set(TRACE_FAIL_LEAK_DETECTED) };
        eprintln!("ALM_TRACE: slot 90 — leak at exit (sys_alloc_count() > 0)");
    }
}

fn elem_layout(len: i64, esize: usize) -> Layout {
    let bytes = usize::try_from(len)
        .ok()
        .and_then(|l| l.checked_mul(esize))
        .unwrap_or_else(|| abort_alloc(usize::MAX));
    Layout::from_size_align(bytes, span_align(esize)).unwrap_or_else(|_| abort_alloc(bytes))
}

const fn span_align(esize: usize) -> usize {
    if esize == u128::ESIZE {
        u128::ALIGN
    } else {
        u64::ALIGN
    }
}

fn abort_alloc(bytes: usize) -> ! {
    eprintln!("alm: table allocation of {bytes} bytes failed");
    std::process::abort();
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_new(esize: usize, flags: u8) -> *mut AlmTable {
    let contains_tables = (flags & 0x80) >> 7;
    let elem_kind = (flags >> 1) & 0x07;
    let is_sparse = (flags & 0x01) != 0;

    let hdr = Box::into_raw(Box::new(AlmTable {
        data: std::ptr::null_mut(),
        len: 0,
        reserve: 0,
        esize,
        mode: if is_sparse {
            TableMode::Sparse
        } else {
            TableMode::Dense
        },
        contains_tables,
        elem_kind,
        sparse_map: if is_sparse {
            Box::into_raw(Box::new(HashMap::new()))
        } else {
            std::ptr::null_mut()
        },
        border: 0,
    }));
    ALLOC_COUNT.fetch_add(1, Ordering::Relaxed);
    TOTAL_COUNT.fetch_add(1, Ordering::Relaxed);
    let id = exec_id();
    unsafe { mirror_census(id) };
    unsafe { alm_trace_set(TRACE_RT_ALLOC) };
    if id == -1
        && LOCAL_LEAK_HOOK
            .compare_exchange(0, 1, Ordering::Relaxed, Ordering::Relaxed)
            .is_ok()
    {
        // registry full: this copy owes its own exit leak check
        unsafe { atexit(alm_trace_leak_check) };
    }
    hdr
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_grow(t: *mut AlmTable, idx: i64) {
    if t.is_null() {
        unsafe { alm_trace_set(TRACE_RT_GROW_NULL) };
        return;
    }
    let tbl = unsafe { &mut *t };
    if tbl.mode != TableMode::Dense {
        return;
    }
    if idx >= 0 && idx == i64::MAX {
        eprintln!("alm fatal: table index overflow (idx={idx})");
        std::process::abort();
    }
    unsafe { span_grow(tbl, idx.wrapping_add(1)) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_reserve(t: *mut AlmTable, n: i64) {
    if t.is_null() {
        unsafe { alm_trace_set(TRACE_RT_RESERVE_NULL) };
        return;
    }
    let raw_esize = unsafe { ptr::addr_of!((*t).esize).read() };
    let raw_len = unsafe { ptr::addr_of!((*t).len).read() };
    let raw_mode = unsafe { ptr::addr_of!((*t).mode).cast::<u8>().read() };
    if raw_esize == FREE_POISON_ESIZE
        || raw_len < 0
        || !matches!(raw_esize, 1 | 8 | 16)
        || raw_mode > 1
    {
        eprintln!(
            "alm fatal: alm_tbl_reserve called on freed or corrupted AlmTable {:p} (len={}, esize=0x{:x}, mode={})",
            t, raw_len, raw_esize, raw_mode
        );
        std::process::abort();
    }

    let tbl = unsafe { &mut *t };
    if tbl.mode != TableMode::Dense {
        return;
    }

    if n > tbl.border {
        tbl.border = n;
    }
    unsafe { span_grow(tbl, n) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_len(t: *const AlmTable) -> i64 {
    if t.is_null() {
        return 0;
    }
    unsafe { (*t).border }
}

pub const SPARSE_THRESHOLD: i64 = 100_000;

#[inline(never)]
unsafe fn overflow_map(tbl: &mut AlmTable) -> &mut HashMap<i64, u128> {
    if tbl.sparse_map.is_null() {
        tbl.sparse_map = Box::into_raw(Box::new(HashMap::with_capacity(1)));
    }
    unsafe { &mut *tbl.sparse_map }
}

mod cell_sealed {
    pub trait Sealed {}
}

pub trait CellRepr: Copy + cell_sealed::Sealed {
    const ESIZE: usize;

    const ALIGN: usize;

    unsafe fn load_slot(slot: *const u8) -> Self;

    fn to_lane(self) -> u128;

    fn from_lane(lane: u128) -> Self;

    unsafe fn store_span(slot: *mut u8, cell: Self);

    unsafe fn load_span(slot: *const u8) -> Self;

    unsafe fn store_dst(cell: Self, dst: *mut u8);
}

impl cell_sealed::Sealed for u8 {}
impl cell_sealed::Sealed for u64 {}
impl cell_sealed::Sealed for u128 {}

impl CellRepr for u8 {
    const ESIZE: usize = 1;
    const ALIGN: usize = 8;
    unsafe fn load_slot(slot: *const u8) -> Self {
        unsafe { *slot }
    }
    fn to_lane(self) -> u128 {
        u128::from(self)
    }
    fn from_lane(lane: u128) -> Self {
        (lane & 0xff) as u8
    }
    unsafe fn store_span(slot: *mut u8, cell: Self) {
        unsafe { slot.write(cell) };
    }
    unsafe fn load_span(slot: *const u8) -> Self {
        unsafe { slot.read() }
    }
    unsafe fn store_dst(cell: Self, dst: *mut u8) {
        unsafe { dst.write(cell) };
    }
}

impl CellRepr for u64 {
    const ESIZE: usize = 8;
    const ALIGN: usize = 8;
    unsafe fn load_slot(slot: *const u8) -> Self {
        unsafe { (slot as *const u64).read() }
    }
    fn to_lane(self) -> u128 {
        u128::from(self)
    }
    fn from_lane(lane: u128) -> Self {
        lane as u64
    }
    unsafe fn store_span(slot: *mut u8, cell: Self) {
        unsafe { (slot as *mut u64).write(cell) };
    }
    unsafe fn load_span(slot: *const u8) -> Self {
        unsafe { (slot as *const u64).read() }
    }
    unsafe fn store_dst(cell: Self, dst: *mut u8) {
        unsafe { (dst as *mut u64).write(cell) };
    }
}

impl CellRepr for u128 {
    const ESIZE: usize = 16;
    const ALIGN: usize = 16;
    unsafe fn load_slot(slot: *const u8) -> Self {
        unsafe { (slot as *const u128).read_unaligned() }
    }
    fn to_lane(self) -> u128 {
        self
    }
    fn from_lane(lane: u128) -> Self {
        lane
    }
    unsafe fn store_span(slot: *mut u8, cell: Self) {
        debug_assert!(slot.addr() & 15 == 0, "u128 span cell not 16-aligned");
        unsafe { (slot as *mut u128).write(cell) };
    }
    unsafe fn load_span(slot: *const u8) -> Self {
        debug_assert!(slot.addr() & 15 == 0, "u128 span cell not 16-aligned");
        unsafe { (slot as *const u128).read() }
    }
    unsafe fn store_dst(cell: Self, dst: *mut u8) {
        unsafe { (dst as *mut u128).write_unaligned(cell) };
    }
}

const _: () = assert!(u8::ESIZE == 1 && u64::ESIZE == 8 && u128::ESIZE == 16);
const _: () = {
    assert!(u8::ALIGN == 8 && u64::ALIGN == 8 && u128::ALIGN == 16);
    assert!(span_align(u8::ESIZE) == u8::ALIGN);
    assert!(span_align(u64::ESIZE) == u64::ALIGN);
    assert!(span_align(u128::ESIZE) == u128::ALIGN);
};

#[derive(Clone, Copy)]
#[allow(dead_code)]
pub struct KeyedCell(u128);

#[allow(dead_code)]
impl cell_sealed::Sealed for KeyedCell {}

#[allow(dead_code)]
impl CellRepr for KeyedCell {
    const ESIZE: usize = 16;
    const ALIGN: usize = 16;
    unsafe fn load_slot(slot: *const u8) -> Self {
        Self(unsafe { (slot as *const u128).read_unaligned() })
    }
    fn to_lane(self) -> u128 {
        self.0
    }
    fn from_lane(lane: u128) -> Self {
        Self(lane)
    }
    unsafe fn store_span(slot: *mut u8, cell: Self) {
        debug_assert!(slot.addr() & 15 == 0, "KeyedCell span cell not 16-aligned");
        unsafe { (slot as *mut u128).write(cell.0) };
    }
    unsafe fn load_span(slot: *const u8) -> Self {
        debug_assert!(slot.addr() & 15 == 0, "KeyedCell span cell not 16-aligned");
        Self(unsafe { (slot as *const u128).read() })
    }
    unsafe fn store_dst(cell: Self, dst: *mut u8) {
        unsafe { (dst as *mut u128).write_unaligned(cell.0) };
    }
}

#[allow(dead_code)]
unsafe fn keyed_set(t: *mut AlmTable, index: i64, cell: KeyedCell) {
    unsafe { set_core::<KeyedCell>(t, index, cell) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_div_zero_guard(rhs: i64) {
    if rhs == 0 {
        unsafe { alm_trace_set(TRACE_FAIL_DIV_ZERO) };
        eprintln!("alm runtime error: attempt to perform 'n/0' (integer division by zero)");
        std::process::abort();
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_set(t: *mut AlmTable, index: i64, val: *const u8) {
    if t.is_null() {
        unsafe { alm_trace_set(TRACE_FAIL_NULL_ROW_STORE) };
        eprintln!("alm runtime error: attempt to index a nil value (null table row)");
        std::process::abort();
    }
    match unsafe { (&*t).esize } {
        1 => unsafe { set_core::<u8>(t, index, u8::load_slot(val)) },
        8 => unsafe { set_core::<u64>(t, index, u64::load_slot(val)) },
        16 => unsafe { set_core::<u128>(t, index, u128::load_slot(val)) },
        other => {
            eprintln!("alm runtime error: AlmTable esize {other} has no cell repr");
            std::process::abort();
        }
    }
}

unsafe fn set_core<C: CellRepr>(t: *mut AlmTable, index: i64, cell: C) {
    let tbl = unsafe { &mut *t };

    // Integer keys are the non-negative span of the i64 lane: negative
    // integers — including any whose bits happen to land in the reserved
    // string-key range — drop silently, the total-store philosophy.
    // String keys cannot reach this core: they enter through
    // set_skey_core from the *_skey entry points, which the compiler
    // selects only for its Reg<StrKey> lane (src/ir.rs), so a user
    // integer can never address a record cell however it was produced.
    if index < 0 {
        return;
    }

    if tbl.mode == TableMode::Sparse {
        tbl.border = tbl.border.max(index.saturating_add(1));
        let map = unsafe { &mut *tbl.sparse_map };
        map.insert(index, cell.to_lane());
        return;
    }

    if index > tbl.len.saturating_add(SPARSE_THRESHOLD) {
        tbl.border = tbl.border.max(index.saturating_add(1));
        unsafe { overflow_map(tbl).insert(index, cell.to_lane()) };
        return;
    }

    tbl.border = tbl.border.max(index.saturating_add(1));
    unsafe { span_grow(tbl, index.wrapping_add(1)) };
    let ptr = unsafe { tbl.data.add(index as usize * C::ESIZE) };
    unsafe { C::store_span(ptr, cell) };
    if !tbl.sparse_map.is_null() {
        unsafe { (&mut *tbl.sparse_map).remove(&index) };
    }
}

/// String-key store: the overflow map only — never border/#t, the dense
/// span, or the mode (a record write on a Dense table is just an
/// overflow insert). The caller is a `*_skey` entry point; the compiler
/// guarantees the key is a negative interned identity, which the
/// debug_assert double-checks.
unsafe fn set_skey_core<C: CellRepr>(t: *mut AlmTable, key: i64, cell: C) {
    debug_assert!(is_str_key(key), "skey store outside the reserved range");
    let tbl = unsafe { &mut *t };
    unsafe { overflow_map(tbl).insert(key, cell.to_lane()) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_get(t: *mut AlmTable, index: i64, dst: *mut u8, esize: usize) {
    if dst.is_null() {
        return;
    }
    if t.is_null() {
        std::ptr::write_bytes(dst, 0, esize);
        return;
    }
    match unsafe { (&*t).esize } {
        1 => unsafe { u8::store_dst(get_core::<u8>(t, index), dst) },
        8 => unsafe { u64::store_dst(get_core::<u64>(t, index), dst) },
        16 => unsafe { u128::store_dst(get_core::<u128>(t, index), dst) },
        other => {
            eprintln!("alm runtime error: AlmTable esize {other} has no cell repr");
            std::process::abort();
        }
    }
}

unsafe fn get_core<C: CellRepr>(t: *mut AlmTable, index: i64) -> C {
    let tbl = unsafe { &mut *t };

    // negative integers (the string-key range included) read the zero
    // lane — string keys never reach this core (see set_core)
    if index < 0 {
        return C::from_lane(0);
    }

    if tbl.mode == TableMode::Sparse {
        let map = unsafe { &mut *tbl.sparse_map };
        return match map.get(&index) {
            Some(&lane) => C::from_lane(lane),
            None => C::from_lane(0),
        };
    }

    if !tbl.sparse_map.is_null()
        && let Some(&lane) = unsafe { (&*tbl.sparse_map).get(&index) }
    {
        return C::from_lane(lane);
    }
    if index >= tbl.len {
        return C::from_lane(0);
    }
    let ptr = unsafe { tbl.data.add(index as usize * C::ESIZE) };
    unsafe { C::load_span(ptr) }
}

/// String-key read: the overflow map only; a missing field reads the
/// zero lane — the same "unset cell" semantics as out-of-range arrays.
unsafe fn get_skey_core<C: CellRepr>(t: *mut AlmTable, key: i64) -> C {
    debug_assert!(is_str_key(key), "skey read outside the reserved range");
    let tbl = unsafe { &mut *t };
    if !tbl.sparse_map.is_null()
        && let Some(&lane) = unsafe { (&*tbl.sparse_map).get(&key) }
    {
        return C::from_lane(lane);
    }
    C::from_lane(0)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_set_any(t: *mut AlmTable, index: i64, val: i128) {
    if t.is_null() {
        unsafe { alm_trace_set(TRACE_FAIL_NULL_ROW_STORE) };
        eprintln!("alm runtime error: attempt to index a nil value (null table row)");
        std::process::abort();
    }
    match unsafe { (&*t).esize } {
        16 => unsafe { set_core::<u128>(t, index, val as u128) },
        other => {
            eprintln!("alm runtime error: AlmTable esize {other} has no register cell face");
            std::process::abort();
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_get_any(t: *mut AlmTable, index: i64) -> i128 {
    if t.is_null() {
        return 0;
    }
    match unsafe { (&*t).esize } {
        16 => unsafe { get_core::<u128>(t, index) as i128 },
        other => {
            eprintln!("alm runtime error: AlmTable esize {other} has no register cell face");
            std::process::abort();
        }
    }
}

// The string-key faces of the same four entry points. The compiler's
// TableKey::Str lane (Reg<StrKey>, src/ir.rs) selects these — the split
// IS the unforgeability guarantee: no integer register can name a record
// cell, because generated integer traffic only ever names the int faces
// above (whose cores drop every negative index).

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_set_skey(t: *mut AlmTable, key: i64, val: *const u8) {
    if t.is_null() {
        unsafe { alm_trace_set(TRACE_FAIL_NULL_ROW_STORE) };
        eprintln!("alm runtime error: attempt to index a nil value (null table row)");
        std::process::abort();
    }
    match unsafe { (&*t).esize } {
        1 => unsafe { set_skey_core::<u8>(t, key, u8::load_slot(val)) },
        8 => unsafe { set_skey_core::<u64>(t, key, u64::load_slot(val)) },
        16 => unsafe { set_skey_core::<u128>(t, key, u128::load_slot(val)) },
        other => {
            eprintln!("alm runtime error: AlmTable esize {other} has no cell repr");
            std::process::abort();
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_get_skey(t: *mut AlmTable, key: i64, dst: *mut u8, esize: usize) {
    if dst.is_null() {
        return;
    }
    if t.is_null() {
        std::ptr::write_bytes(dst, 0, esize);
        return;
    }
    match unsafe { (&*t).esize } {
        1 => unsafe { u8::store_dst(get_skey_core::<u8>(t, key), dst) },
        8 => unsafe { u64::store_dst(get_skey_core::<u64>(t, key), dst) },
        16 => unsafe { u128::store_dst(get_skey_core::<u128>(t, key), dst) },
        other => {
            eprintln!("alm runtime error: AlmTable esize {other} has no cell repr");
            std::process::abort();
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_set_any_skey(t: *mut AlmTable, key: i64, val: i128) {
    if t.is_null() {
        unsafe { alm_trace_set(TRACE_FAIL_NULL_ROW_STORE) };
        eprintln!("alm runtime error: attempt to index a nil value (null table row)");
        std::process::abort();
    }
    match unsafe { (&*t).esize } {
        16 => unsafe { set_skey_core::<u128>(t, key, val as u128) },
        other => {
            eprintln!("alm runtime error: AlmTable esize {other} has no register cell face");
            std::process::abort();
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_get_any_skey(t: *mut AlmTable, key: i64) -> i128 {
    if t.is_null() {
        return 0;
    }
    match unsafe { (&*t).esize } {
        16 => unsafe { get_skey_core::<u128>(t, key) as i128 },
        other => {
            eprintln!("alm runtime error: AlmTable esize {other} has no register cell face");
            std::process::abort();
        }
    }
}

unsafe fn span_grow(tbl: &mut AlmTable, want: i64) {
    if want < 0 {
        return;
    }
    if want <= tbl.len {
        return;
    }
    let new_len = want.max(tbl.len.wrapping_mul(2)).max(8);
    let new_bytes = usize::try_from(new_len)
        .ok()
        .and_then(|l| l.checked_mul(tbl.esize))
        .unwrap_or_else(|| abort_alloc(usize::MAX));
    if tbl.reserve != 0 {
        unsafe { grow_vm(tbl, new_bytes) };
        tbl.len = new_len;
        return;
    }
    if new_bytes >= GRADUATE_AT && vm_enabled() {
        unsafe { graduate(tbl, new_bytes) };
        tbl.len = new_len;
        return;
    }
    let new = elem_layout(new_len, tbl.esize);
    let buf = if tbl.data.is_null() {
        unsafe { alloc_zeroed(new) }
    } else {
        let old = elem_layout(tbl.len, tbl.esize);
        let grown = unsafe { realloc(tbl.data.cast(), old, new.size()) };

        if grown.is_null() {
            abort_alloc(new.size());
        }

        unsafe {
            grown
                .byte_offset((tbl.len * tbl.esize as i64) as isize)
                .write_bytes(0, (new_len - tbl.len) as usize * tbl.esize);
        }
        grown
    };
    tbl.data = buf;
    tbl.len = new_len;
}

const GRADUATE_AT: usize = 1 << 20;
const RESERVE_FLOOR: usize = 1 << 26;
const PAGE: usize = 4096;

const PROT_NONE: i32 = 0x0;
const PROT_READ: i32 = 0x1;
const PROT_WRITE: i32 = 0x2;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const MAP_NORESERVE: i32 = 0x4000;
const MREMAP_MAYMOVE: i32 = 1;

unsafe extern "C" {
    fn mmap(addr: *mut c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64)
    -> *mut c_void;
    fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
    fn munmap(addr: *mut c_void, len: usize) -> i32;
    fn mremap(addr: *mut c_void, old_len: usize, new_len: usize, flags: i32, ...) -> *mut c_void;
    fn atexit(cb: unsafe extern "C" fn()) -> i32;
}

fn reserve_for(bytes: usize) -> usize {
    bytes
        .max(RESERVE_FLOOR)
        .checked_next_power_of_two()
        .unwrap_or_else(|| abort_alloc(usize::MAX))
}

fn is_map_failed(p: *mut c_void) -> bool {
    p.addr() == usize::MAX
}

fn round_up_page(n: usize) -> usize {
    (n + PAGE - 1) & !(PAGE - 1)
}

fn vm_enabled() -> bool {
    use std::sync::atomic::{AtomicU8, Ordering};
    static STATE: AtomicU8 = AtomicU8::new(0);
    match STATE.load(Ordering::Relaxed) {
        1 => true,
        2 => false,
        _ => {
            let off = std::env::var_os("ALM_VM").is_some_and(|v| v == "off" || v == "0");
            STATE.store(if off { 2 } else { 1 }, Ordering::Relaxed);
            !off
        }
    }
}

unsafe fn graduate(tbl: &mut AlmTable, new_bytes: usize) {
    let reserve = reserve_for(new_bytes);
    let vm = unsafe {
        mmap(
            ptr::null_mut(),
            reserve,
            PROT_NONE,
            MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
            -1,
            0,
        )
    };
    if is_map_failed(vm) {
        abort_alloc(reserve);
    }
    let commit = round_up_page(new_bytes);
    if unsafe { mprotect(vm, commit, PROT_READ | PROT_WRITE) } != 0 {
        unsafe { munmap(vm, reserve) };
        abort_alloc(commit);
    }
    if !tbl.data.is_null() {
        unsafe {
            ptr::copy_nonoverlapping(
                tbl.data,
                vm.cast::<u8>(),
                elem_layout(tbl.len, tbl.esize).size(),
            );
            dealloc(tbl.data, elem_layout(tbl.len, tbl.esize));
        }
    }
    tbl.data = vm.cast::<u8>();
    tbl.reserve = reserve;
}

unsafe fn grow_vm(tbl: &mut AlmTable, new_bytes: usize) {
    if new_bytes > tbl.reserve {
        let new_reserve = reserve_for(new_bytes);
        let moved = unsafe { mremap(tbl.data.cast(), tbl.reserve, new_reserve, MREMAP_MAYMOVE) };
        if is_map_failed(moved) {
            abort_alloc(new_reserve);
        }
        tbl.data = moved.cast::<u8>();
        tbl.reserve = new_reserve;
    }
    let commit = round_up_page(new_bytes);
    if unsafe { mprotect(tbl.data.cast(), commit, PROT_READ | PROT_WRITE) } != 0 {
        abort_alloc(commit);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_free(t: *mut AlmTable) {
    unsafe { free_tbl(t, &[]) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_free_except(t: *mut AlmTable, keep: *mut AlmTable) {
    unsafe { free_tbl(t, &[keep]) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_tbl_free_except_n(
    t: *mut AlmTable,
    keeps: *const *mut AlmTable,
    n: usize,
) {
    if keeps.is_null() {
        unsafe { free_tbl(t, &[]) };
        return;
    }
    let slice = unsafe { std::slice::from_raw_parts(keeps, n) };
    unsafe { free_tbl(t, slice) };
}

const FREE_POISON_ESIZE: usize = 0xDEAD_F8EE_DEAD_F8EE;

unsafe fn validate_header_before_free(t: *mut AlmTable, prev_allocs: usize) {
    let raw_data = unsafe { ptr::addr_of!((*t).data).read() };
    let raw_len = unsafe { ptr::addr_of!((*t).len).read() };
    let raw_reserve = unsafe { ptr::addr_of!((*t).reserve).read() };
    let raw_esize = unsafe { ptr::addr_of!((*t).esize).read() };
    let raw_mode = unsafe { ptr::addr_of!((*t).mode).cast::<u8>().read() };
    let raw_contains = unsafe { ptr::addr_of!((*t).contains_tables).read() };
    let raw_elem_kind = unsafe { ptr::addr_of!((*t).elem_kind).read() };
    let raw_sparse = unsafe { ptr::addr_of!((*t).sparse_map).read() };
    let raw_border = unsafe { ptr::addr_of!((*t).border).read() };

    if raw_esize == FREE_POISON_ESIZE {
        eprintln!(
            "alm fatal: DOUBLE FREE of AlmTable header {:p} \
             (tcache next/data={:p}, tcache_key/len=0x{:016x} [{}], prev_alloc_count={})",
            t, raw_data, raw_len as u64, raw_len, prev_allocs
        );
        std::process::abort();
    }

    let valid_esize = matches!(raw_esize, 1 | 8 | 16);
    let valid_mode = matches!(raw_mode, 0 | 1);
    let valid_elem_kind = raw_elem_kind <= ALM_ELEM_UNDECIDED;
    let valid_len = raw_len >= 0
        && usize::try_from(raw_len)
            .ok()
            .and_then(|l| l.checked_mul(raw_esize))
            .is_some();
    let valid_span = (raw_len == 0 && raw_data.is_null())
        || (raw_len > 0 && !raw_data.is_null())
        || raw_mode == 1;

    if prev_allocs == 0
        || !valid_esize
        || !valid_mode
        || !valid_elem_kind
        || !valid_len
        || !valid_span
    {
        eprintln!(
            "alm fatal: corrupted or already-freed AlmTable header at {:p} during free_tbl:\n  \
             prev_alloc_count = {}\n  \
             @0  data            = {:p}\n  \
             @8  len             = {} (0x{:016x})\n  \
             @16 reserve         = {} (0x{:x})\n  \
             @24 esize           = {} (0x{:x})\n  \
             @32 mode            = {}\n  \
             @33 contains_tables = {}\n  \
             @34 elem_kind       = {}\n  \
             @40 sparse_map      = {:p}\n  \
             @48 border          = {}",
            t,
            prev_allocs,
            raw_data,
            raw_len,
            raw_len as u64,
            raw_reserve,
            raw_reserve,
            raw_esize,
            raw_esize,
            raw_mode,
            raw_contains,
            raw_elem_kind,
            raw_sparse,
            raw_border,
        );
        std::process::abort();
    }
}

unsafe fn free_tbl(t: *mut AlmTable, keeps: &[*mut AlmTable]) {
    if t.is_null() || keeps.contains(&t) {
        return;
    }
    unsafe { alm_trace_set(TRACE_RT_FREE) };
    let prev_allocs = ALLOC_COUNT.fetch_sub(1, Ordering::Relaxed);
    unsafe { mirror_census(EXEC_ID.load(Ordering::Relaxed)) };
    unsafe { validate_header_before_free(t, prev_allocs) };
    let mut tbl = unsafe { Box::from_raw(t) };

    let esize = tbl.esize;
    unsafe { ptr::write_volatile(&mut tbl.esize, FREE_POISON_ESIZE) };

    if tbl.contains_tables != 0 {
        let is_valid_ptr = |addr: usize| -> bool {
            #[cfg(target_pointer_width = "64")]
            let is_user_space = addr < 0x0000_7FFF_FFFF_FFFF;
            #[cfg(not(target_pointer_width = "64"))]
            let is_user_space = true;

            addr > 0x0100_0000 && is_user_space && (addr & 7) == 0
        };

        if tbl.mode == TableMode::Dense && !tbl.data.is_null() {
            let ptrs =
                std::slice::from_raw_parts(tbl.data.cast::<*mut AlmTable>(), tbl.len as usize);
            for &child in ptrs {
                if is_valid_ptr(child as usize) {
                    unsafe { alm_trace_set(TRACE_RT_FREE_CHILD) };
                    unsafe { free_tbl(child, keeps) };
                }
            }
        }
        if !tbl.sparse_map.is_null() {
            let map = unsafe { &*tbl.sparse_map };
            for &child_addr in map.values() {
                if is_valid_ptr(child_addr as usize) {
                    unsafe { alm_trace_set(TRACE_RT_FREE_CHILD) };
                    unsafe { free_tbl(child_addr as *mut AlmTable, keeps) };
                }
            }
        }
    }

    if !tbl.sparse_map.is_null() {
        let _ = unsafe {
            Box::from_raw(
                tbl.sparse_map
                    .cast::<std::collections::HashMap<i64, u128>>(),
            )
        };
    }
    if tbl.mode == TableMode::Sparse {
    } else if !tbl.data.is_null() {
        if tbl.reserve != 0 {
            unsafe { munmap(tbl.data.cast(), tbl.reserve) };
        } else {
            unsafe { dealloc(tbl.data, elem_layout(tbl.len, esize)) };
        }
    }

    unsafe {
        ptr::write_volatile(&mut tbl.data, ptr::null_mut());
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_print_int(val: i64) {
    print!("{val}");
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_print_float(val: f64) {
    print!("{val}");
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_print_bool(val: bool) {
    print!("{val}");
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_print_string(val: *const u8) {
    if val.is_null() {
        return;
    }
    let mut len = 0usize;
    unsafe {
        while *val.add(len) != 0 {
            len += 1;
        }
    }
    let bytes = unsafe { std::slice::from_raw_parts(val, len) };
    print!("{}", String::from_utf8_lossy(bytes));
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_str_len(val: *const u8) -> i64 {
    if val.is_null() {
        return 0;
    }
    let mut len = 0usize;
    unsafe {
        while *val.add(len) != 0 {
            len += 1;
        }
    }
    len as i64
}

/* The string pool lives in the substrate (async/str_pool.c) — the third
stateful layer inverted (trace plate, exec registry, strings). One pool
per process: pointer equality is sound across alm copies, and every
pooled string carries its negative table key in an 8-byte prefix.
RT_STR_INTERN / RT_STR_POOL_HIT (slots 8/9) are poked by the substrate
now, anonymously — the pool cannot know the calling copy's exec id. */

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_str_register(ptrs: *const *const u8, n: usize) {
    unsafe { vx_str_register(ptrs as *mut *const u8, n) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_str_intern(s: *const u8, len: usize) -> *const u8 {
    unsafe { vx_str_intern(s, len) }
}

/// The negative table key of a pooled string: one load of the 8-byte
/// prefix. Contract: `s` must be pool-born (interned or registered) —
/// static .rodata literals have no prefix (the backend routes literal
/// handles through strtab slots for exactly this reason).
///
/// A null handle (an unset String cell reads 0 — total-read philosophy,
/// the same null `alm_str_len` guards) answers -1: negative but NOT a
/// str key (top two bits 11, not 10), so set_core no-ops it like any
/// other negative index and get_core reads a zero lane — the store is
/// dropped, the read is 0, and neither the array slot 0 nor the overflow
/// map is polluted. (Answering 0 would alias array slot 0; answering
/// STR_KEY_TAG would alias every null string onto one overflow cell.)
#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_str_key(s: *const u8) -> i64 {
    if s.is_null() {
        return -1;
    }
    unsafe { (s as *const i64).sub(1).read_unaligned() }
}

/// Rust mirror of str_pool.c's derive — an ABI contract, not an
/// implementation detail. The backend's literal-key constant folder must
/// produce identical values. FNV-1a 64 over the NUL-free bytes, masked to
/// 62 bits, tagged into the reserved negative range (top two bits 10).
pub const STR_KEY_TAG: i64 = i64::MIN;

#[inline]
pub fn is_str_key(index: i64) -> bool {
    (index & (3i64 << 62)) == STR_KEY_TAG
}

pub fn str_key_of_bytes(bytes: &[u8]) -> i64 {
    let mut h: u64 = 14695981039346656037;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(1099511628211);
    }
    (STR_KEY_TAG as u64 | (h & 0x3FFF_FFFF_FFFF_FFFF)) as i64
}

#[inline]
fn any_pack(tag: i32, payload: u64) -> i128 {
    ((tag as i64 as i128) << 64) | (payload as i128)
}

#[inline]
fn any_tag(v: i128) -> i32 {
    (v >> 64) as i32
}

#[inline]
fn any_payload(v: i128) -> u64 {
    v as u64
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_any_print(v: i128) {
    match any_tag(v) {
        ALM_ARG_INT => print!("{}", any_payload(v) as i64),
        ALM_ARG_FLOAT => print!("{}", f64::from_bits(any_payload(v))),
        ALM_ARG_BOOL => print!("{}", any_payload(v) != 0),
        ALM_ARG_STRING => {
            let p = any_payload(v) as *const u8;
            if !p.is_null() {
                let bytes = unsafe { cstr_bytes(p) };
                print!("{}", String::from_utf8_lossy(bytes));
            }
        }
        _ => print!("{}", any_payload(v) as i64),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_any_eq(l: i128, r: i128) -> i32 {
    i32::from(l == r)
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_any_len(v: i128) -> i64 {
    let kind_word = |k: i32| match k {
        ALM_ARG_INT => "int",
        ALM_ARG_FLOAT => "float",
        ALM_ARG_BOOL => "bool",
        ALM_ARG_STRING => "string",
        _ => "unknown",
    };
    match any_tag(v) {
        ALM_ARG_STRING => {
            let p = any_payload(v) as *const u8;
            if p.is_null() {
                return 0;
            }
            unsafe { alm_str_len(p) }
        }
        k => {
            unsafe { alm_trace_set(TRACE_FAIL_ANY_LEN) };
            eprintln!(
                "alm runtime error: alm_any_len: '#' demands a string cell, got kind {} ({})",
                k,
                kind_word(k)
            );
            std::process::abort();
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_any_from_int(v: i64) -> i128 {
    any_pack(ALM_ARG_INT, v as u64)
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_any_from_float(v: f64) -> i128 {
    any_pack(ALM_ARG_FLOAT, v.to_bits())
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_any_from_bool(v: bool) -> i128 {
    any_pack(ALM_ARG_BOOL, u64::from(v))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_any_from_str(p: *const u8) -> i128 {
    any_pack(ALM_ARG_STRING, p as u64)
}

pub enum AnyWord {
    Int(i64),
    Float(f64),
    Bool(bool),
    Str,
}

pub fn classify_word(w: &[u8]) -> AnyWord {
    if let Ok(s) = std::str::from_utf8(w) {
        if let Ok(v) = s.parse::<i64>() {
            return AnyWord::Int(v);
        }
        if let Ok(v) = s.parse::<f64>() {
            return AnyWord::Float(v);
        }
        match s {
            "true" => return AnyWord::Bool(true),
            "false" => return AnyWord::Bool(false),
            _ => {}
        }
    }
    AnyWord::Str
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_any_pack(tag: i32, payload: u64) -> i128 {
    any_pack(tag, payload)
}

unsafe fn any_of_word(w: &[u8]) -> i128 {
    match classify_word(w) {
        AnyWord::Int(v) => any_pack(ALM_ARG_INT, v as u64),
        AnyWord::Float(v) => any_pack(ALM_ARG_FLOAT, v.to_bits()),
        AnyWord::Bool(v) => any_pack(ALM_ARG_BOOL, u64::from(v)),
        AnyWord::Str => {
            let p = unsafe { alm_str_intern(w.as_ptr(), w.len()) };
            any_pack(ALM_ARG_STRING, p as u64)
        }
    }
}

unsafe fn cstr_bytes(p: *const u8) -> &'static [u8] {
    let mut len = 0usize;
    unsafe {
        while *p.add(len) != 0 {
            len += 1;
        }
    }
    unsafe { std::slice::from_raw_parts(p, len) }
}

pub const ALM_ARG_NONE: i32 = -1;
pub const ALM_ARG_INT: i32 = 0;
pub const ALM_ARG_FLOAT: i32 = 1;
pub const ALM_ARG_BOOL: i32 = 2;
pub const ALM_ARG_STRING: i32 = 3;
pub const ALM_ARG_ANY: i32 = 4;

pub const ALM_ELEM_TABLE: u8 = 5;
pub const ALM_ELEM_UNDECIDED: u8 = 6;

pub fn arg_kind_of(elem: &crate::AlmElem) -> i32 {
    match elem {
        crate::AlmElem::Float => ALM_ARG_FLOAT,
        crate::AlmElem::Boolean => ALM_ARG_BOOL,
        crate::AlmElem::String => ALM_ARG_STRING,
        crate::AlmElem::Any => ALM_ARG_ANY,
        crate::AlmElem::Integer => ALM_ARG_INT,
    }
}

pub fn elem_of_kind(kind: i32) -> Option<crate::AlmElem> {
    match kind {
        ALM_ARG_INT => Some(crate::AlmElem::Integer),
        ALM_ARG_FLOAT => Some(crate::AlmElem::Float),
        ALM_ARG_BOOL => Some(crate::AlmElem::Boolean),
        ALM_ARG_STRING => Some(crate::AlmElem::String),
        ALM_ARG_ANY => Some(crate::AlmElem::Any),
        _ => None,
    }
}

fn arg_kind_words(kind: i32) -> &'static str {
    match kind {
        ALM_ARG_FLOAT => "numbers (64-bit floats)",
        ALM_ARG_BOOL => "booleans ('true'/'false')",
        ALM_ARG_STRING => "strings (any word)",
        ALM_ARG_ANY => "int, float, bool, or string words",
        _ => "integers (64-bit)",
    }
}

fn arg_kind_table(kind: i32) -> &'static str {
    match kind {
        ALM_ARG_FLOAT => "Table<Float>",
        ALM_ARG_BOOL => "Table<Boolean>",
        ALM_ARG_STRING => "Table<String>",
        ALM_ARG_ANY => "Table<Any>",
        _ => "Table<Integer>",
    }
}

unsafe fn set_word(t: *mut AlmTable, i: i64, w: &[u8], kind: i32) -> Result<(), ()> {
    match kind {
        ALM_ARG_INT => {
            let v: i64 = String::from_utf8_lossy(w).parse().map_err(|_| ())?;
            unsafe { alm_tbl_set(t, i, (&v as *const i64).cast()) };
        }
        ALM_ARG_FLOAT => {
            let v: f64 = String::from_utf8_lossy(w).parse().map_err(|_| ())?;
            unsafe { alm_tbl_set(t, i, (&v as *const f64).cast()) };
        }
        ALM_ARG_BOOL => {
            let v = match w {
                b"true" => 1u8,
                b"false" => 0u8,
                _ => return Err(()),
            };
            unsafe { alm_tbl_set(t, i, (&v as *const u8).cast()) };
        }
        ALM_ARG_STRING => {
            let p = unsafe { alm_str_intern(w.as_ptr(), w.len()) };
            unsafe { alm_tbl_set(t, i, (&p as *const *const u8).cast()) };
        }
        ALM_ARG_ANY => {
            let v = unsafe { any_of_word(w) };
            unsafe { alm_tbl_set_any(t, i, v) };
        }
        _ => return Err(()),
    }
    Ok(())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_exec_main(
    argc: i32,
    argv: *const *const u8,
    kind: i32,
    exec: unsafe extern "C" fn(*mut AlmTable) -> *mut AlmTable,
) -> i32 {
    // the exe registers before any code runs (its constructors precede
    // every dlopen), so the main binary deterministically takes slot 0
    IS_EXE.store(true, Ordering::Relaxed);
    let id = exec_id();
    let rc = unsafe { exec_main_inner(argc, argv, kind, exec) };
    if id >= 0 {
        unsafe { vx_exec_state_set(id, 3) }; // VX_EXEC_FINISHED
    }
    rc
}

unsafe fn exec_main_inner(
    argc: i32,
    argv: *const *const u8,
    kind: i32,
    exec: unsafe extern "C" fn(*mut AlmTable) -> *mut AlmTable,
) -> i32 {
    if kind == ALM_ARG_NONE {
        let result = exec(std::ptr::null_mut());
        unsafe { alm_tbl_free(result) };
        return 0;
    }
    let mut words: Vec<&[u8]> = Vec::new();
    if !argv.is_null() {
        for i in 1..(argc.max(0) as usize) {
            let p = unsafe { *argv.add(i) };
            if !p.is_null() {
                words.push(unsafe { cstr_bytes(p) });
            }
        }
    }
    let esize = match kind {
        ALM_ARG_BOOL => 1,
        ALM_ARG_ANY => 16,
        _ => 8,
    };
    let args = unsafe { alm_tbl_new(esize, ((kind as u8) & 0x07) << 1) };
    for (i, w) in words.iter().enumerate() {
        if unsafe { set_word(args, i as i64, w, kind) }.is_err() {
            eprintln!(
                "alm error: boundary args must be {}, got '{}' — the arg table is {}",
                arg_kind_words(kind),
                String::from_utf8_lossy(w),
                arg_kind_table(kind),
            );
            unsafe { alm_tbl_free(args) };
            return 1;
        }
    }
    let result = exec(args);
    unsafe {
        if result != args {
            alm_tbl_free(args);
        }
        alm_tbl_free(result);
    }
    0
}

const RTLD_NOW: i32 = 0x2;
const RTLD_LOCAL: i32 = 0x1;

unsafe extern "C" {
    fn dlopen(filename: *const i8, flags: i32) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const i8) -> *mut c_void;
    fn dlerror() -> *const i8;
}

unsafe fn ffi_open_path(path: *const u8) -> Vec<u8> {
    let bytes = unsafe { cstr_bytes(path) };
    if bytes.contains(&b'/') {
        return Vec::new();
    }
    let mut prefixed = Vec::with_capacity(bytes.len() + 3);
    prefixed.push(b'.');
    prefixed.push(b'/');
    prefixed.extend_from_slice(bytes);
    prefixed.push(0);
    prefixed
}

unsafe fn ffi_dlsym_or_die(lib: *mut c_void, name: *const u8) -> *mut c_void {
    let sym = unsafe { dlsym(lib, name.cast()) };
    if sym.is_null() {
        unsafe { alm_trace_set(TRACE_FAIL_FFI_SYM) };
        let shown = if name.is_null() {
            "(null)".to_string()
        } else {
            String::from_utf8_lossy(unsafe { cstr_bytes(name) }).into_owned()
        };
        eprintln!("alm fatal: ffi could not find symbol '{shown}' in the loaded module");
        std::process::abort();
    }
    sym
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_ffi_load(path: *const u8) -> *mut c_void {
    if path.is_null() {
        eprintln!("alm fatal: ffi.load called with a null path");
        std::process::abort();
    }
    let prefixed = unsafe { ffi_open_path(path) };
    let direct = prefixed.is_empty();
    let handle = unsafe {
        dlopen(
            if direct {
                path.cast()
            } else {
                prefixed.as_ptr().cast()
            },
            RTLD_NOW | RTLD_LOCAL,
        )
    };
    if handle.is_null() {
        unsafe { alm_trace_set(TRACE_FAIL_FFI_LOAD) };
        let err = unsafe {
            let e = dlerror();
            if e.is_null() {
                String::new()
            } else {
                String::from_utf8_lossy(cstr_bytes(e.cast())).into_owned()
            }
        };
        eprintln!(
            "alm fatal: ffi.load could not open '{}' ({err})",
            String::from_utf8_lossy(unsafe { cstr_bytes(path) }),
        );
        std::process::abort();
    }
    unsafe { alm_trace_set(TRACE_RT_FFI_LOAD) };
    handle
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_ffi_arg_kind(lib: *mut c_void) -> i64 {
    if lib.is_null() {
        eprintln!("alm fatal: ffi use of a null library handle");
        std::process::abort();
    }
    let sym = unsafe { ffi_dlsym_or_die(lib, c"alm_arg_kind".as_ptr() as *const u8) };
    let f = unsafe { std::mem::transmute_copy::<*mut c_void, unsafe extern "C" fn() -> i32>(&sym) };
    unsafe { f() as i64 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_ffi_call(lib: *mut c_void, sym: *const u8, arg: *mut AlmTable) {
    if lib.is_null() {
        eprintln!("alm fatal: ffi call on a null library handle");
        std::process::abort();
    }
    let exec = unsafe {
        std::mem::transmute_copy::<*mut c_void, unsafe extern "C" fn(*mut AlmTable) -> *mut AlmTable>(
            &ffi_dlsym_or_die(lib, sym),
        )
    };
    let result = unsafe { exec(arg) };
    if result.is_null() || result == arg {
        return;
    }
    let free_fn = unsafe {
        std::mem::transmute_copy::<*mut c_void, unsafe extern "C" fn(*mut AlmTable)>(
            &ffi_dlsym_or_die(lib, c"alm_tbl_free".as_ptr() as *const u8),
        )
    };
    unsafe { free_fn(result) };
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_print_sep() {
    print!("\t");
}

#[unsafe(no_mangle)]
pub extern "C" fn alm_print_nl() {
    println!();
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_alloc_count() -> i64 {
    ALLOC_COUNT.load(Ordering::Relaxed) as i64
}

/// The dialect's window into the shared C11 session: how many alm
/// runtimes (this exe + every loaded .so module) have registered in the
/// process — reads the exec registry owned by libalm_async.so, not this
/// copy's state.
#[unsafe(no_mangle)]
pub extern "C" fn sys_exec_count() -> i64 {
    unsafe { vx_exec_count() as i64 }
}

/// The coroutine thread wrapper's FINISHED hook: this copy's exec handle
/// in the shared registry (the substrate calls it after alm_exec returns
/// on the worker thread).
#[unsafe(no_mangle)]
pub extern "C" fn alm_rt_exec_id() -> i32 {
    EXEC_ID.load(Ordering::Relaxed)
}

// --- the coroutine.* parody's runtime face ---------------------------------
//
// The substrate owns threads, lanes, and packets; these wrappers marshal
// table cells on the CALLER's thread/heap (read-only borrows — no
// AlmTable pointer ever crosses a thread) and intern the status words.

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_coro_create(lib: *mut c_void) -> i64 {
    let id = unsafe { vx_coro_create(lib) };
    if id < 0 {
        unsafe { alm_trace_set(TRACE_FAIL_CORO_CREATE) };
    }
    id as i64
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_coro_resume(co: i64, t: *mut AlmTable) -> i64 {
    let id = co as i32;
    if id < 0 {
        // R9: slot exhaustion must NEVER masquerade as the EOF sentinel
        // (a drained lane's -1). A negative handle can only come from an
        // exhausted create — a loud, distinct death, not a silent
        // truncation.
        unsafe { alm_trace_set(TRACE_FAIL_CORO_CREATE) };
        eprintln!(
            "alm fatal: coroutine.resume on handle {co} — the coroutine registry \
             was exhausted at create time (all lanes live); test \
             coroutine.create's result before resuming"
        );
        std::process::abort();
    }
    if unsafe { vx_coro_status(id) } == 1 && !t.is_null() {
        // VX_CORO_CREATED: marshal t[0..2] as the spawn inputs (reads on
        // this thread, this heap); later resumes' tables are ignored
        let mut lanes = [0u64; 3];
        for (i, lane) in lanes.iter_mut().enumerate() {
            let mut buf = [0u8; 16];
            unsafe { alm_tbl_get(t, i as i64, buf.as_mut_ptr(), 16) };
            *lane = u64::from_ne_bytes(buf[..8].try_into().unwrap());
        }
        unsafe { vx_coro_send(id, lanes[0], lanes[1], lanes[2]) };
    }
    let r = unsafe {
        vx_coro_start(id);
        alm_trace_set(TRACE_CORO_SPAWN);
        vx_coro_pull(id)
    };
    unsafe {
        alm_trace_set(if r < 0 {
            TRACE_CORO_DEAD
        } else {
            TRACE_CORO_RESUME
        })
    };
    r
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_coro_yield(value: i64) -> i64 {
    let r = unsafe { vx_coro_yield(value as u64) };
    unsafe {
        alm_trace_set(if r < 0 {
            TRACE_CORO_YIELD_DROPPED
        } else {
            TRACE_CORO_YIELD
        })
    };
    r
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_coro_status(co: i64) -> *const u8 {
    // the parody's punchline, straight-faced: "running" because it IS —
    // on its own pthread (CREATED answers Lua's "suspended")
    let word: &[u8] = match unsafe { vx_coro_status(co as i32) } {
        1 => b"suspended",
        2 => b"running",
        _ => b"dead",
    };
    unsafe { alm_str_intern(word.as_ptr(), word.len()) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn alm_coro_close(co: i64) -> i64 {
    unsafe { alm_trace_set(TRACE_CORO_CLOSE) };
    unsafe { vx_coro_join(co as i32) };
    0
}

#[cfg(test)]
mod strkey_tests {
    use super::*;

    /// Records are overflow cells addressed by negative interned
    /// identities through the dedicated skey faces. The three invariants
    /// that make them safe on Dense tables: `#t` (border) is untouched,
    /// the dense span is untouched, and the value round-trips through
    /// the overflow map.
    #[test]
    fn negative_keys_never_pollute_border() {
        for flags in [0u8, 1u8] {
            // 0 = Dense, 1 = Sparse — record writes behave identically
            let t = unsafe { alm_tbl_new(std::mem::size_of::<i128>(), flags) };
            let key = str_key_of_bytes(b"health");

            unsafe { alm_tbl_set_any(t, 0, 41) }; // array cell (int face)
            unsafe { alm_tbl_set_any(t, 1, 7) };
            unsafe { alm_tbl_set_any_skey(t, key, alm_any_pack(3, 0x1234)) }; // record cell

            assert_eq!(
                unsafe { alm_tbl_len(t) },
                2,
                "record write must not touch #t"
            );
            assert_eq!(
                unsafe { alm_tbl_get_any_skey(t, key) },
                alm_any_pack(3, 0x1234)
            );
            assert_eq!(unsafe { alm_tbl_get_any(t, 0) }, 41);
            assert_eq!(unsafe { alm_tbl_get_any(t, 1) }, 7);
            assert_eq!(
                unsafe { alm_tbl_get_any_skey(t, str_key_of_bytes(b"missing")) },
                0
            );
            // free per iteration: unit tests must not feed the exit-time
            // leak tripwire — sys_alloc_count() is a CI signal, not noise
            unsafe { alm_tbl_free(t) };
        }
    }

    /// THE unforgeability pin: an i64 whose bits land in the reserved
    /// string-key range, driven through the INTEGER faces (the only
    /// faces generated integer traffic can name), drops like any other
    /// negative index — it must not create, read, or alias a record
    /// cell, no matter how a running program computed it.
    #[test]
    fn str_range_integers_drop_through_the_int_faces() {
        let t = unsafe { alm_tbl_new(std::mem::size_of::<i128>(), 0) };
        let forged = str_key_of_bytes(b"health");
        assert!(is_str_key(forged));

        unsafe { alm_tbl_set_any(t, forged, alm_any_pack(3, 0x1234)) };
        assert_eq!(
            unsafe { alm_tbl_len(t) },
            0,
            "a forged str-range int must not grow #t"
        );
        assert_eq!(
            unsafe { alm_tbl_get_any_skey(t, str_key_of_bytes(b"health")) },
            0,
            "a forged str-range int must not create the record cell"
        );
        assert_eq!(
            unsafe { alm_tbl_get_any(t, forged) },
            0,
            "a forged str-range int reads the zero lane, not a cell"
        );
        unsafe { alm_tbl_free(t) };
    }

    #[test]
    fn interned_strings_carry_their_key_in_the_prefix() {
        let a = unsafe { alm_str_intern(b"player".as_ptr(), 6) };
        let b = unsafe { alm_str_intern(b"player".as_ptr(), 6) };
        assert_eq!(a, b, "intern dedup within the process pool");

        let key = unsafe { alm_str_key(a) };
        assert!(is_str_key(key), "pooled strings carry negative str keys");
        assert_eq!(key, str_key_of_bytes(b"player"), "prefix cache == derive");

        // the handle stays a valid C-string: prefix is invisible to readers
        assert_eq!(unsafe { alm_str_len(a) }, 6);
        assert_eq!(unsafe { *a }, b'p');
    }

    #[test]
    fn key_derive_is_stable_and_disjoint_from_program_integers() {
        let k1 = str_key_of_bytes(b"health");
        let k2 = str_key_of_bytes(b"health");
        assert_eq!(k1, k2);
        assert_ne!(str_key_of_bytes(b"health"), str_key_of_bytes(b"wealth"));
        assert!(k1 < 0);
        assert!(is_str_key(k1));
        assert!(!is_str_key(-1) && !is_str_key(-42) && !is_str_key(5));
    }
}
