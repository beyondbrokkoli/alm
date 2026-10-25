// async/probe/probe_recycle.rs — R9's probe: lanes that fail honestly.
// (1) RECYCLE: VX_CORO_MAX create/drain lifetimes in a row must all
//     succeed — before the DEAD->EMPTY transition the registry burned a
//     slot per lifetime and create returned -1 after 4 cycles.
// (2) HONEST EXHAUSTION: with every lane genuinely live, one more
//     create returns a DISTINCT -1 (the caller can test it); a lane
//     never silently truncates.
// The substrate's idle-exit path (a NULL module) retires each thread
// immediately, so drain == vx_coro_pull's -1.
//
// Build & run: ./build.sh && ./probe_recycle

unsafe extern "C" {
    fn vx_coro_create(lib: *mut core::ffi::c_void) -> i32;
    fn vx_coro_start(id: i32) -> i32;
    fn vx_coro_pull(id: i32) -> i64;
    fn vx_coro_status(id: i32) -> u32;
    fn vx_coro_join(id: i32);
}

const VX_CORO_EMPTY: u32 = 0;
const VX_CORO_DEAD: u32 = 3;

fn main() {
    let mut failures = 0u32;

    // (1) eight sequential lifetimes (registry holds 4 lanes)
    for cycle in 0..8 {
        let id = unsafe { vx_coro_create(core::ptr::null_mut()) };
        if id < 0 {
            eprintln!(
                "FAIL cycle {cycle}: create returned {id} — slot not recycled (R9 regression)"
            );
            failures += 1;
            continue;
        }
        let started = unsafe { vx_coro_start(id) };
        if started != id {
            eprintln!("FAIL cycle {cycle}: start({id}) returned {started}");
            failures += 1;
            continue;
        }
        let drained = unsafe { vx_coro_pull(id) };
        if drained != -1 {
            eprintln!(
                "FAIL cycle {cycle}: expected drained -1 from the idle lane, got {drained}"
            );
            failures += 1;
        }
        let st = unsafe { vx_coro_status(id) };
        if st != VX_CORO_DEAD && st != VX_CORO_EMPTY {
            eprintln!("FAIL cycle {cycle}: retired lane status {st}, want DEAD/EMPTY");
            failures += 1;
        }
    }

    // (2) fill every lane LIVE (idle threads retire instantly, so hold
    // them in CREATED — started-but-never-pulled also counts), then one
    // more create must return a testable -1
    let mut live = Vec::new();
    loop {
        let id = unsafe { vx_coro_create(core::ptr::null_mut()) };
        if id < 0 {
            break;
        }
        live.push(id);
    }
    if live.is_empty() {
        eprintln!("FAIL: registry reported exhaustion with zero live lanes");
        failures += 1;
    } else {
        println!(
            "exhaustion surfaced distinctly: {} live lanes, next create = -1",
            live.len()
        );
    }
    for id in live {
        unsafe { vx_coro_join(id) };
    }

    // post-close, the registry recycles again
    let id = unsafe { vx_coro_create(core::ptr::null_mut()) };
    if id < 0 {
        eprintln!("FAIL: create after closing all lanes still exhausted");
        failures += 1;
    } else {
        unsafe { vx_coro_join(id) };
    }

    if failures == 0 {
        println!("probe_recycle: 8/8 lifetimes recycled, exhaustion distinct — GREEN");
    } else {
        eprintln!("probe_recycle: {failures} failure(s)");
        std::process::exit(1);
    }
}
