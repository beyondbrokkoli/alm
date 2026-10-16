#![allow(unsafe_op_in_unsafe_fn)]
use std::alloc::{Layout, alloc_zeroed, dealloc, realloc};
use std::collections::HashMap;
use std::ffi::c_void;
use std::fs::OpenOptions;
use std::os::unix::io::AsRawFd;
use std::ptr;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

use crate::trace::{
    TRACE_FAIL_ANY_LEN, TRACE_FAIL_DIV_ZERO, TRACE_FAIL_FFI_LOAD, TRACE_FAIL_FFI_SYM,
    TRACE_FAIL_LEAK_DETECTED, TRACE_FAIL_NULL_ROW_STORE, TRACE_RT_ALLOC, TRACE_RT_FFI_LOAD,
    TRACE_RT_FREE, TRACE_RT_FREE_CHILD, TRACE_RT_GROW_NULL, TRACE_RT_RESERVE_NULL,
    TRACE_RT_STR_INTERN, TRACE_RT_STR_POOL_HIT,
};

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TableMode {
    Dense = 0,
    Sparse = 1,
}

/// #[repr(C)] header. Field layout (offset: type), ABI-pinned by the
#[repr(C)]
pub struct GlmTable {
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
        size_of::<GlmTable>() == 56,
        "GlmTable must stay the 56-byte ABI"
    );
    assert!(offset_of!(GlmTable, data) == 0);
    assert!(offset_of!(GlmTable, len) == 8);
    assert!(offset_of!(GlmTable, reserve) == 16);
    assert!(offset_of!(GlmTable, esize) == 24);
    assert!(offset_of!(GlmTable, mode) == 32);
    assert!(offset_of!(GlmTable, contains_tables) == 33);
    assert!(offset_of!(GlmTable, elem_kind) == 34);
    assert!(offset_of!(GlmTable, sparse_map) == 40);
    assert!(offset_of!(GlmTable, border) == 48);
};

static ALLOC_COUNT: AtomicUsize = AtomicUsize::new(0);

const TRACE_SLOTS: usize = 256;
const TRACE_FILE: &str = ".glm_rt_trace.bin";

static TRACE_MAP: AtomicPtr<u8> = AtomicPtr::new(ptr::null_mut());
static LEAK_HOOK: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

fn sidecar_mapped_in_this_process() -> bool {
    std::fs::read_to_string("/proc/self/maps")
        .is_ok_and(|maps| maps.lines().any(|l| l.contains(TRACE_FILE)))
}

pub unsafe fn init_trace_map() {
    if !sidecar_mapped_in_this_process() {
        let _ = std::fs::remove_file(TRACE_FILE);
    }
    let Ok(file) = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(TRACE_FILE)
    else {
        return;
    };
    let _ = file.set_len(TRACE_SLOTS as u64);
    let ptr = unsafe {
        mmap(
            ptr::null_mut(),
            TRACE_SLOTS,
            PROT_READ | PROT_WRITE,
            MAP_SHARED,
            file.as_raw_fd(),
            0,
        )
    };
    if is_map_failed(ptr) {
        return;
    }
    TRACE_MAP.store(ptr.cast::<u8>(), Ordering::Relaxed);
}

#[inline]
fn trace_map() -> *mut u8 {
    let map = TRACE_MAP.load(Ordering::Relaxed);
    if !map.is_null() {
        return map;
    }
    unsafe { init_trace_map() };
    TRACE_MAP.load(Ordering::Relaxed)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_trace_set(slot: u8) {
    let map = trace_map();
    if !map.is_null() {
        unsafe { *map.add(slot as usize) = 1 };
    }
}

unsafe extern "C" fn glm_trace_leak_check() {
    if ALLOC_COUNT.load(Ordering::Relaxed) > 0 {
        unsafe { glm_trace_set(TRACE_FAIL_LEAK_DETECTED) };
        eprintln!("GLM_TRACE: slot 90 — leak at exit (sys_alloc_count() > 0)");
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
    eprintln!("glm: table allocation of {bytes} bytes failed");
    std::process::abort();
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_new(esize: usize, flags: u8) -> *mut GlmTable {
    let contains_tables = (flags & 0x80) >> 7;
    let elem_kind = (flags >> 1) & 0x07;
    let is_sparse = (flags & 0x01) != 0;

    let hdr = Box::into_raw(Box::new(GlmTable {
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
    unsafe { glm_trace_set(TRACE_RT_ALLOC) };
    if LEAK_HOOK
        .compare_exchange(0, 1, Ordering::Relaxed, Ordering::Relaxed)
        .is_ok()
    {
        unsafe { atexit(glm_trace_leak_check) };
    }
    hdr
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_grow(t: *mut GlmTable, idx: i64) {
    if t.is_null() {
        unsafe { glm_trace_set(TRACE_RT_GROW_NULL) };
        return;
    }
    let tbl = unsafe { &mut *t };
    if tbl.mode != TableMode::Dense {
        return;
    }
    if idx >= 0 && idx == i64::MAX {
        eprintln!("glm fatal: table index overflow (idx={idx})");
        std::process::abort();
    }
    unsafe { span_grow(tbl, idx.wrapping_add(1)) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_reserve(t: *mut GlmTable, n: i64) {
    if t.is_null() {
        unsafe { glm_trace_set(TRACE_RT_RESERVE_NULL) };
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
            "glm fatal: glm_tbl_reserve called on freed or corrupted GlmTable {:p} (len={}, esize=0x{:x}, mode={})",
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
pub unsafe extern "C" fn glm_tbl_len(t: *const GlmTable) -> i64 {
    if t.is_null() {
        return 0;
    }
    unsafe { (*t).border }
}

pub const SPARSE_THRESHOLD: i64 = 100_000;

#[inline(never)]
unsafe fn overflow_map(tbl: &mut GlmTable) -> &mut HashMap<i64, u128> {
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
unsafe fn keyed_set(t: *mut GlmTable, index: i64, cell: KeyedCell) {
    unsafe { set_core::<KeyedCell>(t, index, cell) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_div_zero_guard(rhs: i64) {
    if rhs == 0 {
        unsafe { glm_trace_set(TRACE_FAIL_DIV_ZERO) };
        eprintln!("glm runtime error: attempt to perform 'n/0' (integer division by zero)");
        std::process::abort();
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_set(t: *mut GlmTable, index: i64, val: *const u8) {
    if t.is_null() {
        unsafe { glm_trace_set(TRACE_FAIL_NULL_ROW_STORE) };
        eprintln!("glm runtime error: attempt to index a nil value (null table row)");
        std::process::abort();
    }
    match unsafe { (&*t).esize } {
        1 => unsafe { set_core::<u8>(t, index, u8::load_slot(val)) },
        8 => unsafe { set_core::<u64>(t, index, u64::load_slot(val)) },
        16 => unsafe { set_core::<u128>(t, index, u128::load_slot(val)) },
        other => {
            eprintln!("glm runtime error: GlmTable esize {other} has no cell repr");
            std::process::abort();
        }
    }
}

unsafe fn set_core<C: CellRepr>(t: *mut GlmTable, index: i64, cell: C) {
    let tbl = unsafe { &mut *t };

    if tbl.mode == TableMode::Sparse {
        if index < 0 {
            return;
        }
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

    if index < 0 {
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

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_get(t: *mut GlmTable, index: i64, dst: *mut u8, esize: usize) {
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
            eprintln!("glm runtime error: GlmTable esize {other} has no cell repr");
            std::process::abort();
        }
    }
}

unsafe fn get_core<C: CellRepr>(t: *mut GlmTable, index: i64) -> C {
    let tbl = unsafe { &mut *t };

    if tbl.mode == TableMode::Sparse {
        if index < 0 {
            return C::from_lane(0);
        }
        let map = unsafe { &mut *tbl.sparse_map };
        return match map.get(&index) {
            Some(&lane) => C::from_lane(lane),
            None => C::from_lane(0),
        };
    }

    if index >= 0
        && !tbl.sparse_map.is_null()
        && let Some(&lane) = unsafe { (&*tbl.sparse_map).get(&index) }
    {
        return C::from_lane(lane);
    }
    if index < 0 || index >= tbl.len {
        return C::from_lane(0);
    }
    let ptr = unsafe { tbl.data.add(index as usize * C::ESIZE) };
    unsafe { C::load_span(ptr) }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_set_any(t: *mut GlmTable, index: i64, val: i128) {
    if t.is_null() {
        unsafe { glm_trace_set(TRACE_FAIL_NULL_ROW_STORE) };
        eprintln!("glm runtime error: attempt to index a nil value (null table row)");
        std::process::abort();
    }
    match unsafe { (&*t).esize } {
        16 => unsafe { set_core::<u128>(t, index, val as u128) },
        other => {
            eprintln!("glm runtime error: GlmTable esize {other} has no register cell face");
            std::process::abort();
        }
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_get_any(t: *mut GlmTable, index: i64) -> i128 {
    if t.is_null() {
        return 0;
    }
    match unsafe { (&*t).esize } {
        16 => unsafe { get_core::<u128>(t, index) as i128 },
        other => {
            eprintln!("glm runtime error: GlmTable esize {other} has no register cell face");
            std::process::abort();
        }
    }
}

unsafe fn span_grow(tbl: &mut GlmTable, want: i64) {
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
const MAP_SHARED: i32 = 0x01;
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
            let off = std::env::var_os("GLM_VM").is_some_and(|v| v == "off" || v == "0");
            STATE.store(if off { 2 } else { 1 }, Ordering::Relaxed);
            !off
        }
    }
}

unsafe fn graduate(tbl: &mut GlmTable, new_bytes: usize) {
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

unsafe fn grow_vm(tbl: &mut GlmTable, new_bytes: usize) {
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
pub unsafe extern "C" fn glm_tbl_free(t: *mut GlmTable) {
    unsafe { free_tbl(t, &[]) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_free_except(t: *mut GlmTable, keep: *mut GlmTable) {
    unsafe { free_tbl(t, &[keep]) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_tbl_free_except_n(
    t: *mut GlmTable,
    keeps: *const *mut GlmTable,
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

unsafe fn validate_header_before_free(t: *mut GlmTable, prev_allocs: usize) {
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
            "glm fatal: DOUBLE FREE of GlmTable header {:p} \
             (tcache next/data={:p}, tcache_key/len=0x{:016x} [{}], prev_alloc_count={})",
            t, raw_data, raw_len as u64, raw_len, prev_allocs
        );
        std::process::abort();
    }

    let valid_esize = matches!(raw_esize, 1 | 8 | 16);
    let valid_mode = matches!(raw_mode, 0 | 1);
    let valid_elem_kind = raw_elem_kind <= GLM_ELEM_UNDECIDED;
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
            "glm fatal: corrupted or already-freed GlmTable header at {:p} during free_tbl:\n  \
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

unsafe fn free_tbl(t: *mut GlmTable, keeps: &[*mut GlmTable]) {
    if t.is_null() || keeps.contains(&t) {
        return;
    }
    unsafe { glm_trace_set(TRACE_RT_FREE) };
    let prev_allocs = ALLOC_COUNT.fetch_sub(1, Ordering::Relaxed);
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
                std::slice::from_raw_parts(tbl.data.cast::<*mut GlmTable>(), tbl.len as usize);
            for &child in ptrs {
                if is_valid_ptr(child as usize) {
                    unsafe { glm_trace_set(TRACE_RT_FREE_CHILD) };
                    unsafe { free_tbl(child, keeps) };
                }
            }
        }
        if !tbl.sparse_map.is_null() {
            let map = unsafe { &*tbl.sparse_map };
            for &child_addr in map.values() {
                if is_valid_ptr(child_addr as usize) {
                    unsafe { glm_trace_set(TRACE_RT_FREE_CHILD) };
                    unsafe { free_tbl(child_addr as *mut GlmTable, keeps) };
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
pub extern "C" fn glm_print_int(val: i64) {
    print!("{val}");
}

#[unsafe(no_mangle)]
pub extern "C" fn glm_print_float(val: f64) {
    print!("{val}");
}

#[unsafe(no_mangle)]
pub extern "C" fn glm_print_bool(val: bool) {
    print!("{val}");
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_print_string(val: *const u8) {
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
pub unsafe extern "C" fn glm_str_len(val: *const u8) -> i64 {
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

use std::sync::Mutex;

static STR_POOL: Mutex<Option<HashMap<Vec<u8>, usize>>> = Mutex::new(None);

fn str_pool() -> std::sync::MutexGuard<'static, Option<HashMap<Vec<u8>, usize>>> {
    let mut guard = STR_POOL.lock().unwrap_or_else(|e| e.into_inner());
    if guard.is_none() {
        *guard = Some(HashMap::new());
    }
    guard
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_str_register(ptrs: *const *const u8, n: usize) {
    let mut pool = str_pool();
    let Some(map) = pool.as_mut() else {
        return;
    };
    for i in 0..n {
        let p = unsafe { *ptrs.add(i) };
        if p.is_null() {
            continue;
        }
        let bytes = unsafe { cstr_bytes(p) };
        map.entry(bytes.to_vec()).or_insert(p as usize);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_str_intern(s: *const u8, len: usize) -> *const u8 {
    let bytes = unsafe { std::slice::from_raw_parts(s, len) };
    {
        let pool = str_pool();
        if let Some(&addr) = pool.as_ref().and_then(|m| m.get(bytes)) {
            unsafe { glm_trace_set(TRACE_RT_STR_POOL_HIT) };
            return addr as *const u8;
        }
    }
    unsafe { glm_trace_set(TRACE_RT_STR_INTERN) };
    let mut buf = Vec::with_capacity(len + 1);
    buf.extend_from_slice(bytes);
    buf.push(0);
    let p = Box::into_raw(buf.into_boxed_slice()) as *const u8;
    let mut pool = str_pool();
    if let Some(map) = pool.as_mut() {
        map.insert(bytes.to_vec(), p as usize);
    }
    p
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
pub extern "C" fn glm_any_print(v: i128) {
    match any_tag(v) {
        GLM_ARG_INT => print!("{}", any_payload(v) as i64),
        GLM_ARG_FLOAT => print!("{}", f64::from_bits(any_payload(v))),
        GLM_ARG_BOOL => print!("{}", any_payload(v) != 0),
        GLM_ARG_STRING => {
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
pub extern "C" fn glm_any_eq(l: i128, r: i128) -> i32 {
    i32::from(l == r)
}

#[unsafe(no_mangle)]
pub extern "C" fn glm_any_len(v: i128) -> i64 {
    let kind_word = |k: i32| match k {
        GLM_ARG_INT => "int",
        GLM_ARG_FLOAT => "float",
        GLM_ARG_BOOL => "bool",
        GLM_ARG_STRING => "string",
        _ => "unknown",
    };
    match any_tag(v) {
        GLM_ARG_STRING => {
            let p = any_payload(v) as *const u8;
            if p.is_null() {
                return 0;
            }
            unsafe { glm_str_len(p) }
        }
        k => {
            unsafe { glm_trace_set(TRACE_FAIL_ANY_LEN) };
            eprintln!(
                "glm runtime error: glm_any_len: '#' demands a string cell, got kind {} ({})",
                k,
                kind_word(k)
            );
            std::process::abort();
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn glm_any_from_int(v: i64) -> i128 {
    any_pack(GLM_ARG_INT, v as u64)
}

#[unsafe(no_mangle)]
pub extern "C" fn glm_any_from_float(v: f64) -> i128 {
    any_pack(GLM_ARG_FLOAT, v.to_bits())
}

#[unsafe(no_mangle)]
pub extern "C" fn glm_any_from_bool(v: bool) -> i128 {
    any_pack(GLM_ARG_BOOL, u64::from(v))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_any_from_str(p: *const u8) -> i128 {
    any_pack(GLM_ARG_STRING, p as u64)
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
pub extern "C" fn glm_any_pack(tag: i32, payload: u64) -> i128 {
    any_pack(tag, payload)
}

unsafe fn any_of_word(w: &[u8]) -> i128 {
    match classify_word(w) {
        AnyWord::Int(v) => any_pack(GLM_ARG_INT, v as u64),
        AnyWord::Float(v) => any_pack(GLM_ARG_FLOAT, v.to_bits()),
        AnyWord::Bool(v) => any_pack(GLM_ARG_BOOL, u64::from(v)),
        AnyWord::Str => {
            let p = unsafe { glm_str_intern(w.as_ptr(), w.len()) };
            any_pack(GLM_ARG_STRING, p as u64)
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

pub const GLM_ARG_NONE: i32 = -1;
pub const GLM_ARG_INT: i32 = 0;
pub const GLM_ARG_FLOAT: i32 = 1;
pub const GLM_ARG_BOOL: i32 = 2;
pub const GLM_ARG_STRING: i32 = 3;
pub const GLM_ARG_ANY: i32 = 4;

pub const GLM_ELEM_TABLE: u8 = 5;
pub const GLM_ELEM_UNDECIDED: u8 = 6;

pub fn arg_kind_of(elem: &crate::GlmElem) -> i32 {
    match elem {
        crate::GlmElem::Float => GLM_ARG_FLOAT,
        crate::GlmElem::Boolean => GLM_ARG_BOOL,
        crate::GlmElem::String => GLM_ARG_STRING,
        crate::GlmElem::Any => GLM_ARG_ANY,
        crate::GlmElem::Integer => GLM_ARG_INT,
    }
}

pub fn elem_of_kind(kind: i32) -> Option<crate::GlmElem> {
    match kind {
        GLM_ARG_INT => Some(crate::GlmElem::Integer),
        GLM_ARG_FLOAT => Some(crate::GlmElem::Float),
        GLM_ARG_BOOL => Some(crate::GlmElem::Boolean),
        GLM_ARG_STRING => Some(crate::GlmElem::String),
        GLM_ARG_ANY => Some(crate::GlmElem::Any),
        _ => None,
    }
}

fn arg_kind_words(kind: i32) -> &'static str {
    match kind {
        GLM_ARG_FLOAT => "numbers (64-bit floats)",
        GLM_ARG_BOOL => "booleans ('true'/'false')",
        GLM_ARG_STRING => "strings (any word)",
        GLM_ARG_ANY => "int, float, bool, or string words",
        _ => "integers (64-bit)",
    }
}

fn arg_kind_table(kind: i32) -> &'static str {
    match kind {
        GLM_ARG_FLOAT => "Table<Float>",
        GLM_ARG_BOOL => "Table<Boolean>",
        GLM_ARG_STRING => "Table<String>",
        GLM_ARG_ANY => "Table<Any>",
        _ => "Table<Integer>",
    }
}

unsafe fn set_word(t: *mut GlmTable, i: i64, w: &[u8], kind: i32) -> Result<(), ()> {
    match kind {
        GLM_ARG_INT => {
            let v: i64 = String::from_utf8_lossy(w).parse().map_err(|_| ())?;
            unsafe { glm_tbl_set(t, i, (&v as *const i64).cast()) };
        }
        GLM_ARG_FLOAT => {
            let v: f64 = String::from_utf8_lossy(w).parse().map_err(|_| ())?;
            unsafe { glm_tbl_set(t, i, (&v as *const f64).cast()) };
        }
        GLM_ARG_BOOL => {
            let v = match w {
                b"true" => 1u8,
                b"false" => 0u8,
                _ => return Err(()),
            };
            unsafe { glm_tbl_set(t, i, (&v as *const u8).cast()) };
        }
        GLM_ARG_STRING => {
            let p = unsafe { glm_str_intern(w.as_ptr(), w.len()) };
            unsafe { glm_tbl_set(t, i, (&p as *const *const u8).cast()) };
        }
        GLM_ARG_ANY => {
            let v = unsafe { any_of_word(w) };
            unsafe { glm_tbl_set_any(t, i, v) };
        }
        _ => return Err(()),
    }
    Ok(())
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_exec_main(
    argc: i32,
    argv: *const *const u8,
    kind: i32,
    exec: unsafe extern "C" fn(*mut GlmTable) -> *mut GlmTable,
) -> i32 {
    if kind == GLM_ARG_NONE {
        let result = exec(std::ptr::null_mut());
        unsafe { glm_tbl_free(result) };
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
        GLM_ARG_BOOL => 1,
        GLM_ARG_ANY => 16,
        _ => 8,
    };
    let args = unsafe { glm_tbl_new(esize, ((kind as u8) & 0x07) << 1) };
    for (i, w) in words.iter().enumerate() {
        if unsafe { set_word(args, i as i64, w, kind) }.is_err() {
            eprintln!(
                "glm error: boundary args must be {}, got '{}' — the arg table is {}",
                arg_kind_words(kind),
                String::from_utf8_lossy(w),
                arg_kind_table(kind),
            );
            unsafe { glm_tbl_free(args) };
            return 1;
        }
    }
    let result = exec(args);
    unsafe {
        if result != args {
            glm_tbl_free(args);
        }
        glm_tbl_free(result);
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
        unsafe { glm_trace_set(TRACE_FAIL_FFI_SYM) };
        let shown = if name.is_null() {
            "(null)".to_string()
        } else {
            String::from_utf8_lossy(unsafe { cstr_bytes(name) }).into_owned()
        };
        eprintln!("glm fatal: ffi could not find symbol '{shown}' in the loaded module");
        std::process::abort();
    }
    sym
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_ffi_load(path: *const u8) -> *mut c_void {
    if path.is_null() {
        eprintln!("glm fatal: ffi.load called with a null path");
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
        unsafe { glm_trace_set(TRACE_FAIL_FFI_LOAD) };
        let err = unsafe {
            let e = dlerror();
            if e.is_null() {
                String::new()
            } else {
                String::from_utf8_lossy(cstr_bytes(e.cast())).into_owned()
            }
        };
        eprintln!(
            "glm fatal: ffi.load could not open '{}' ({err})",
            String::from_utf8_lossy(unsafe { cstr_bytes(path) }),
        );
        std::process::abort();
    }
    unsafe { glm_trace_set(TRACE_RT_FFI_LOAD) };
    handle
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_ffi_arg_kind(lib: *mut c_void) -> i64 {
    if lib.is_null() {
        eprintln!("glm fatal: ffi use of a null library handle");
        std::process::abort();
    }
    let sym = unsafe { ffi_dlsym_or_die(lib, c"glm_arg_kind".as_ptr() as *const u8) };
    let f = unsafe { std::mem::transmute_copy::<*mut c_void, unsafe extern "C" fn() -> i32>(&sym) };
    unsafe { f() as i64 }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn glm_ffi_call(lib: *mut c_void, sym: *const u8, arg: *mut GlmTable) {
    if lib.is_null() {
        eprintln!("glm fatal: ffi call on a null library handle");
        std::process::abort();
    }
    let exec = unsafe {
        std::mem::transmute_copy::<*mut c_void, unsafe extern "C" fn(*mut GlmTable) -> *mut GlmTable>(
            &ffi_dlsym_or_die(lib, sym),
        )
    };
    let result = unsafe { exec(arg) };
    if result.is_null() || result == arg {
        return;
    }
    let free_fn = unsafe {
        std::mem::transmute_copy::<*mut c_void, unsafe extern "C" fn(*mut GlmTable)>(
            &ffi_dlsym_or_die(lib, c"glm_tbl_free".as_ptr() as *const u8),
        )
    };
    unsafe { free_fn(result) };
}

#[unsafe(no_mangle)]
pub extern "C" fn glm_print_sep() {
    print!("\t");
}

#[unsafe(no_mangle)]
pub extern "C" fn glm_print_nl() {
    println!();
}

#[unsafe(no_mangle)]
pub extern "C" fn sys_alloc_count() -> i64 {
    ALLOC_COUNT.load(Ordering::Relaxed) as i64
}
