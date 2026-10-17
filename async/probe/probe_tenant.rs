// async/probe/probe_tenant.rs — exercises the glm tenant & trace layer of
// libglm_async.so: deterministic exec registration (lowest free slot), the
// census mirror, the sole-owner sticky plate, and the chronology ring.
// Runs from any CWD; creates .glm_rt_trace.bin next to the CWD (dev scratch).

use std::ffi::{c_char, CStr};

unsafe extern "C" {
    fn vx_exec_register(name: *const c_char, flags: u32) -> i32;
    fn vx_exec_name(id: i32) -> *const c_char;
    fn vx_exec_state_get(id: i32) -> u32;
    fn vx_exec_state_set(id: i32, state: u32);
    fn vx_exec_flags_get(id: i32) -> u32;
    fn vx_exec_census_set(id: i32, live: i64, total: i64);
    fn vx_exec_count() -> i32;
    fn vx_exec_dump();
    fn vx_trace_poke_exec(exec_id: i32, slot: u8);
    fn vx_trace_poke(slot: u8);
    fn vx_trace_fired(slot: u8) -> u8;
    fn vx_trace_event_count() -> u64;
    fn vx_trace_event_get(seq: u64) -> u32;
}

fn name_of(id: i32) -> String {
    unsafe { CStr::from_ptr(vx_exec_name(id)) }
        .to_string_lossy()
        .into_owned()
}

fn main() {
    // deterministic lowest-free allocation: main exe first, then modules
    let a = unsafe { vx_exec_register(c"main.exe".as_ptr(), 0x1) };
    let b = unsafe { vx_exec_register(c"worker.so".as_ptr(), 0x2) };
    let c = unsafe { vx_exec_register(c"leaky.so".as_ptr(), 0x2) };
    assert_eq!((a, b, c), (0, 1, 2), "exec slots must allocate 0,1,2");
    assert_eq!(unsafe { vx_exec_count() }, 3);
    assert_eq!(name_of(b), "worker.so");
    assert_eq!(unsafe { vx_exec_flags_get(a) }, 0x1);
    assert_eq!(unsafe { vx_exec_state_get(a) }, 2 /* RUNNING */);

    // census mirror + lifecycle transitions
    unsafe { vx_exec_census_set(b, 6, 10) };
    unsafe { vx_exec_state_set(c, 3 /* FINISHED */) };
    assert_eq!(unsafe { vx_exec_state_get(c) }, 3);
    assert_eq!(name_of(99), "");

    // sticky plate: exec-tagged + anonymous (foreign C companion) pokes
    // share the one MAP_SHARED file the .so owns
    unsafe { vx_trace_poke_exec(a, 50) };
    unsafe { vx_trace_poke_exec(b, 60) };
    unsafe { vx_trace_poke(162) };
    assert_eq!(unsafe { vx_trace_fired(50) }, 1);
    assert_eq!(unsafe { vx_trace_fired(60) }, 1);
    assert_eq!(unsafe { vx_trace_fired(162) }, 1);
    assert_eq!(unsafe { vx_trace_fired(90) }, 0, "no leak poked");

    // chronology ring: (exec << 8) | slot, anonymous = 0xFF tag
    let n = unsafe { vx_trace_event_count() };
    assert_eq!(n, 3);
    assert_eq!(unsafe { vx_trace_event_get(0) }, 50);
    assert_eq!(unsafe { vx_trace_event_get(1) }, (1u32 << 8) | 60);
    assert_eq!(unsafe { vx_trace_event_get(2) }, (0xFFu32 << 8) | 162);
    assert_eq!(
        unsafe { vx_trace_event_get(3) },
        0xFFFF_FFFF,
        "unwritten event must read NONE"
    );

    unsafe { vx_exec_dump() };
    println!("probe_tenant: 3 execs registered, plate + ring verified");
}
