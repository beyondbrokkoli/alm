// async/probe/probe.rs — minimal proof: Rust drives the vendored C11 async
// core (mailbox snapshot + CAS ring stream) across two OS threads through ONE
// shared object. Producer = "game thread" posting packets, consumer = "render
// thread" walking the rotation. No mutexes, no tokio, no async/await — the
// atomics in async are the entire runtime.
//
// Build & run: ./build.sh && ./probe

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
    fn vx_key_get(win_id: i32, key: i32) -> u8;
    fn vx_key_set(win_id: i32, key: i32, val: u8);
    fn vx_mouse_dx_get(win_id: i32) -> f32;
    fn vx_mouse_delta_set(win_id: i32, dx: f32, dy: f32);
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
        if a % 10_000 == 0 {
            unsafe {
                vx_key_set(0, 7, (a & 0xff) as u8);
                vx_mouse_delta_set(0, a as f32, -(a as f32));
            }
        }
        produced += 1;
    }
}

fn main() {
    unsafe { vx_init_mailbox() };

    let t0 = Instant::now();
    let game = thread::spawn(producer);

    // Consumer mirrors vk_render_loop.c: gate+advance via vx_stream_next,
    // then the 3-lane active_ring_slots discipline: a consumed slot stays
    // locked until its lane is reused by a later frame. Steady state holds
    // 3 slots, the producer always finds exactly one free (the 3+1 rule).
    let frame_slots: usize = 3;
    let mut active_slots = [-1i32; 10];
    let mut t_frame: u64 = 0;

    let mut spin = 0i32;
    let mut consumed = 0u64;
    let mut expect_seq = 0u64;
    loop {
        if consumed == FRAMES {
            break;
        }
        let read_idx = unsafe { vx_stream_next(0) };
        if read_idx < 0 {
            unsafe { vx_spin_wait(&mut spin) };
            continue;
        }
        spin = 0;
        let current = (t_frame % frame_slots as u64) as usize;
        let finished = active_slots[current];
        if finished != -1 && finished != read_idx {
            unsafe { vx_stream_release(0, finished) };
        }
        active_slots[current] = read_idx;

        let pkt = unsafe { vx_stream_packet(read_idx) };
        let p = unsafe { *pkt };
        assert_eq!(p.crc, fnv(p.a, p.b, p.c), "crc mismatch at seq {}", p.seq);
        assert_eq!(p.seq, expect_seq, "out-of-order delivery: {}", p.seq);
        expect_seq += 1;
        t_frame += 1;
        consumed += 1;
    }
    for slot in active_slots {
        if slot != -1 {
            unsafe { vx_stream_release(0, slot) };
        }
    }

    game.join().expect("producer panicked");
    let dt = t0.elapsed();

    let key = unsafe { vx_key_get(0, 7) };
    let mouse = unsafe { vx_mouse_dx_get(0) };

    println!("frames piped : {consumed} (in order, crc verified)");
    println!("mailbox LWW  : key[7]={key}, mouse_dx={mouse}");
    println!("wall time    : {dt:?}  ({:.0} packets/s)", FRAMES as f64 / dt.as_secs_f64());
    assert_eq!(consumed, FRAMES);
    assert!(key != 0, "mailbox snapshot never delivered");
    assert!(mouse > 0.0, "mouse delta never delivered");
    println!("PROBE PASSED — Rust <-> C11 async core seam is live");
}
