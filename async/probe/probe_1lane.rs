// async/probe/probe_1lane.rs — the regression canary for the acquire fix.
// This is the configuration that exposed the race: a consumer holding ONE
// slot (release previous on advance) while the producer sprints — before the
// fix it skipped a frame roughly once per 4k; it must stay green now that
// vx_stream_acquire only ever takes (ready+1)%4.
//
// Build & run: ./build.sh && ./probe_1lane

use std::thread;
use std::time::Instant;

#[repr(C)]
#[derive(Clone, Copy)]
struct RingPacket {
    seq: u64,
    a: u64,
    b: u64,
    c: u64,
    crc: u64,
}

unsafe extern "C" {
    fn vx_init_mailbox();
    fn vx_stream_acquire(win_id: i32) -> i32;
    fn vx_stream_commit(win_id: i32, idx: i32);
    fn vx_stream_release(win_id: i32, idx: i32);
    fn vx_stream_next(win_id: i32) -> i32;
    fn vx_stream_packet(idx: i32) -> *mut RingPacket;
    fn vx_spin_wait(spin_count: *mut i32);
}

const FRAMES: u64 = 200_000;

fn fnv(a: u64, b: u64, c: u64) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325u64;
    for lane in [a, b, c] {
        h ^= lane;
        h = h.wrapping_mul(0x100_0000_01b3);
    }
    h
}

fn producer() {
    let mut spin = 0i32;
    let mut produced = 0u64;
    while produced < FRAMES {
        let idx = unsafe { vx_stream_acquire(0) };
        if idx < 0 {
            unsafe { vx_spin_wait(&mut spin) };
            continue;
        }
        spin = 0;
        let a = produced;
        let b = a.wrapping_mul(3).wrapping_add(7);
        let c = a ^ 0xdead_beef;
        unsafe {
            let pkt = vx_stream_packet(idx);
            (*pkt).seq = a;
            (*pkt).a = a;
            (*pkt).b = b;
            (*pkt).c = c;
            (*pkt).crc = fnv(a, b, c);
            vx_stream_commit(0, idx);
        }
        produced += 1;
    }
}

fn main() {
    unsafe { vx_init_mailbox() };

    let t0 = Instant::now();
    let game = thread::spawn(producer);

    let mut spin = 0i32;
    let mut consumed = 0u64;
    let mut expect_seq = 0u64;
    let mut held: i32 = -1;
    loop {
        if consumed == FRAMES {
            break;
        }
        let idx = unsafe { vx_stream_next(0) };
        if idx < 0 {
            unsafe { vx_spin_wait(&mut spin) };
            continue;
        }
        spin = 0;
        let p = unsafe { *vx_stream_packet(idx) };
        assert_eq!(p.crc, fnv(p.a, p.b, p.c), "crc mismatch at seq {}", p.seq);
        assert_eq!(p.seq, expect_seq, "out-of-order delivery: {}", p.seq);
        expect_seq += 1;
        if held != -1 && held != idx {
            unsafe { vx_stream_release(0, held) };
        }
        held = idx;
        consumed += 1;
    }
    if held != -1 {
        unsafe { vx_stream_release(0, held) };
    }

    game.join().expect("producer panicked");
    let dt = t0.elapsed();
    println!("1-lane: {consumed} frames in order, crc verified, {dt:?} ({:.0} packets/s)",
        FRAMES as f64 / dt.as_secs_f64());
    println!("CANARY PASSED — out-of-rotation write is gone");
}
