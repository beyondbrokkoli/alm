use std::ffi::c_void;
use std::ptr;
use std::sync::atomic::{AtomicPtr, AtomicU32, Ordering};

include!(concat!(env!("OUT_DIR"), "/trace_signals.rs"));

const TRACE_FILE: &str = ".glm_trace.bin";
pub const TRACE_RING_CAPACITY: u32 = 8192;
const TRACE_FIRED_OFF: usize = 0;
const TRACE_CAPACITY_OFF: usize = 4;
const TRACE_RING_OFF: usize = 8;
const TRACE_PLATE_LEN: usize = TRACE_RING_OFF + TRACE_RING_CAPACITY as usize;

static TRACE_MAP: AtomicPtr<u8> = AtomicPtr::new(ptr::null_mut());

const PROT_READ: i32 = 0x1;
const PROT_WRITE: i32 = 0x2;
const MAP_SHARED: i32 = 0x01;

unsafe extern "C" {
    fn mmap(addr: *mut c_void, len: usize, prot: i32, flags: i32, fd: i32, off: i64)
    -> *mut c_void;
}

fn is_map_failed(p: *mut c_void) -> bool {
    p.addr() == usize::MAX
}

pub fn compiler_trace_init() {
    use std::fs::OpenOptions;
    use std::os::unix::io::AsRawFd;
    let _ = std::fs::remove_file(TRACE_FILE);
    if let Ok(file) = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(TRACE_FILE)
    {
        let _ = file.set_len(TRACE_PLATE_LEN as u64);
        let ptr = unsafe {
            mmap(
                ptr::null_mut(),
                TRACE_PLATE_LEN,
                PROT_READ | PROT_WRITE,
                MAP_SHARED,
                file.as_raw_fd(),
                0,
            )
        };
        if !is_map_failed(ptr) {
            let map = ptr.cast::<u8>();
            TRACE_MAP.store(map, Ordering::SeqCst);
            unsafe {
                (map.add(TRACE_CAPACITY_OFF) as *mut u32).write(TRACE_RING_CAPACITY);
            }
        }
    }
}

pub fn compiler_trace_signal(slot: u8) {
    let map = TRACE_MAP.load(Ordering::Relaxed);
    if map.is_null() {
        return;
    }
    unsafe {
        let seq = (*map.add(TRACE_FIRED_OFF).cast::<AtomicU32>()).fetch_add(1, Ordering::Relaxed);
        let ring_idx = TRACE_RING_OFF + (seq as usize % TRACE_RING_CAPACITY as usize);
        *map.add(ring_idx) = slot;
    }
}

#[macro_export]
macro_rules! signal {
    ($slot:expr) => {
        $crate::trace::compiler_trace_signal($slot)
    };
    ($gate:expr,$slot:expr) => {
        if $gate {
            $crate::trace::compiler_trace_signal($slot)
        }
    };
}
