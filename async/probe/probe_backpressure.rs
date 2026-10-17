// async/probe/probe_backpressure.rs — the deterministic blocking-path
// proof for one 4-slot ring lane: fill it single-threaded, watch a
// producer thread freeze inside the exact spin vx_coro_yield runs, then
// free slots one at a time through the 1-lane discipline and watch the
// producer climb by EXACTLY one per freed slot, FIFO seq order verified
// through slot wraparound.
//
// Evidence channel: vx_stream_dump snapshots at every phase (nothing new
// added — the dump's ready_idx/local_read/locked_mask + per-slot seq IS
// the rotation record) plus exact producer/consumer counters.
//
// The invariant ladder, exact numbers (a broken gate fails these long
// before any timing matters):
//   fill    : 4 committed; acquire-on-full answers -1 (single-threaded)
//   block   : 300ms with no consumer -> produced frozen at 4, producer
//             observed "full" thousands of times
//   hold    : consume #1 advances local_read but frees NOTHING (the held
//             slot is the discipline) -> still frozen at 4
//   resume  : consume #2 releases slot 0 -> produced climbs to exactly 5
//   ladder  : one more refill per consume -> 6, 7, 8; the consumer reads
//             seq 1..8 strictly in order, including the refill packet
//             that landed in the REUSED slot 0 after wraparound
//
// Build & run: ./build.sh && ./probe_backpressure

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;
use std::time::Duration;

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
    fn vx_stream_dump(win_id: i32);
    fn vx_spin_wait(spin_count: *mut i32);
}

const LANE: i32 = 0;

static PRODUCED: AtomicU64 = AtomicU64::new(0);
static FULL_HITS: AtomicU64 = AtomicU64::new(0);
static STOP: AtomicBool = AtomicBool::new(false);

/// generous scheduling slack for the producer's tiered backoff to wake
/// (the spin escalates to 1ms sleeps, so 50ms is ~25x the worst wake)
fn settle() {
    thread::sleep(Duration::from_millis(50));
}

fn write_packet(idx: i32, seq: u64) {
    unsafe {
        let pkt = vx_stream_packet(idx);
        (*pkt).seq = seq;
        (*pkt).a = seq;
        (*pkt).b = 0;
        (*pkt).c = 0;
        (*pkt).crc = seq;
        vx_stream_commit(LANE, idx);
    }
}

/// vx_coro_yield's producer loop, verbatim discipline: spin on -1 with
/// the shared tiered backoff, publish on success
fn producer() {
    let mut spin = 0i32;
    loop {
        if STOP.load(Ordering::Relaxed) {
            return;
        }
        let idx = unsafe { vx_stream_acquire(LANE) };
        if idx < 0 {
            FULL_HITS.fetch_add(1, Ordering::Relaxed);
            unsafe { vx_spin_wait(&mut spin) };
            continue;
        }
        spin = 0;
        let seq = PRODUCED.fetch_add(1, Ordering::Relaxed) + 1;
        write_packet(idx, seq);
    }
}

fn assert_produced(want: u64, phase: &str) {
    let got = PRODUCED.load(Ordering::Relaxed);
    if got != want {
        unsafe { vx_stream_dump(LANE) };
        panic!("{phase}: produced {got}, want exactly {want}");
    }
}

/// gate+advance+read, holding the just-consumed slot and releasing the
/// previous (probe_1lane's discipline — the 1-lane floor)
fn consume(expect_seq: u64, held: &mut i32) {
    let idx = unsafe { vx_stream_next(LANE) };
    assert!(idx >= 0, "consumer starved while packets stood committed");
    let p = unsafe { *vx_stream_packet(idx) };
    assert_eq!(
        p.seq,
        expect_seq,
        "FIFO order broken: got seq {}, wanted {}",
        p.seq,
        expect_seq
    );
    if *held != -1 && *held != idx {
        unsafe { vx_stream_release(LANE, *held) };
    }
    *held = idx;
}

fn main() {
    unsafe { vx_init_mailbox() };

    // [fill] single-threaded: 4 commits, then the full gate must refuse
    // (PRODUCED counts every commit, main thread's fill included, so the
    // later frozen-window assertion reads the same ledger the producer
    // thread continues from)
    for _ in 0..4u64 {
        let idx = unsafe { vx_stream_acquire(LANE) };
        assert!(idx >= 0, "empty lane refused acquire");
        let seq = PRODUCED.fetch_add(1, Ordering::Relaxed) + 1;
        write_packet(idx, seq);
    }
    let full = unsafe { vx_stream_acquire(LANE) };
    assert_eq!(full, -1, "acquire on a full lane must answer -1");
    println!("[fill]    4 committed; acquire-on-full -> -1 (single-threaded)");
    unsafe { vx_stream_dump(LANE) };

    // [block] the producer thread must freeze inside its spin
    let prod = thread::spawn(producer);
    thread::sleep(Duration::from_millis(300));
    assert_produced(4, "[block] frozen window");
    let hits = FULL_HITS.load(Ordering::Relaxed);
    assert!(hits >= 200, "producer never observed full ({hits} hits)");
    println!("[block]  300ms: produced frozen at 4; producer saw 'full' {hits} times");
    unsafe { vx_stream_dump(LANE) };

    // [hold] consume #1 advances local_read but frees nothing
    let mut held: i32 = -1;
    consume(1, &mut held);
    settle();
    assert_produced(4, "[hold] first consume must free nothing");
    println!("[hold]   consume #1 (seq 1): slot held, none freed — still 4");
    unsafe { vx_stream_dump(LANE) };

    // [resume] consume #2 releases slot 0 — exactly one refill
    consume(2, &mut held);
    settle();
    assert_produced(5, "[resume] one freed slot must mean exactly one refill");
    println!("[resume] consume #2 (seq 2) freed slot 0: produced climbed to exactly 5");
    unsafe { vx_stream_dump(LANE) };

    // [ladder] +1 per consume; seq 5 is the refill that landed in the
    // reused slot 0 — FIFO verified through the wraparound
    for (expect_seq, want) in [(3u64, 6u64), (4u64, 7u64), (5u64, 8u64)] {
        consume(expect_seq, &mut held);
        settle();
        assert_produced(want, "[ladder]");
    }
    println!("[ladder] +1 per consume: 6, 7, 8 — seq order 1..8 held through wraparound");

    STOP.store(true, Ordering::Relaxed);
    prod.join().expect("producer panicked");
    if held != -1 {
        unsafe { vx_stream_release(LANE, held) };
    }
    println!("BACKPRESSURE PASSED — producer blocks on full, resumes on free, +1 per slot");
}
