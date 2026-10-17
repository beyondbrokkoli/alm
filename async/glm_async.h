#ifndef GLM_ASYNC_H
#define GLM_ASYNC_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

#define VX_MAX_WINDOWS 4
#define VX_RING_SIZE   16

/* --- glm tenant & trace layer (glm-owned additions, not engine-vendored) ---
   One .so per OS process (the loader's guarantee) owns every piece of
   process-wide glm state: the multi-exec registry, the trace plate file,
   and the exit-time leak report. Per-artifact glm_rt copies hold only
   their exec_id handle. */

#define VX_EXEC_MAX          8
#define VX_EXEC_NAME_MAX     56
#define VX_TRACE_SLOTS       256   /* must match the plate SSOT (1 byte/slot) */
#define VX_TRACE_RING_CAP    8192
#define VX_TRACE_EVENT_NONE  0xFFFFFFFFu

#define VX_EXEC_EMPTY    0u
#define VX_EXEC_BOOTING  1u
#define VX_EXEC_RUNNING  2u
#define VX_EXEC_FINISHED 3u
#define VX_EXEC_FAILED   4u

#define VX_EXEC_F_EXE 0x1u   /* a --exe glm binary (glm_exec_main world) */
#define VX_EXEC_F_SO  0x2u   /* a glm shared module (driven over the C ABI) */

/* must match FAIL_LEAK_DETECTED in trace_signals.txt (the SSOT lives in
   the Rust crate; the substrate hardcodes the one slot it owns) */
#define VX_TRACE_SLOT_LEAK 90

typedef struct {
    uint64_t seq;
    uint64_t a;
    uint64_t b;
    uint64_t c;
    uint64_t crc;
} RingPacket;

void vx_init_mailbox(void);

int  vx_stream_acquire(int win_id);
void vx_stream_commit(int win_id, int idx);
void vx_stream_release(int win_id, int idx);
int  vx_stream_next(int win_id);
void vx_stream_dump(int win_id);
RingPacket* vx_stream_packet(int idx);

void vx_spin_wait(int* spin_count);

uint8_t vx_key_get(int win_id, int key);
void    vx_key_set(int win_id, int key, uint8_t val);
float   vx_mouse_dx_get(int win_id);
void    vx_mouse_delta_set(int win_id, float dx, float dy);
int     vx_running_get(void);
void    vx_running_set(int running);

/* ---- exec registry: register on load/init (lowest free slot wins; the exe's
   constructors run before any dlopen, so the main binary is exec 0) */
void        vx_async_ready(void);
int32_t     vx_exec_register(const char* name, uint32_t flags); /* -> id or -1 (full) */
const char* vx_exec_name(int32_t id);
uint32_t    vx_exec_state_get(int32_t id);
void        vx_exec_state_set(int32_t id, uint32_t state);
uint32_t    vx_exec_flags_get(int32_t id);
void        vx_exec_census_set(int32_t id, int64_t live, int64_t total);
int32_t     vx_exec_count(void);
void        vx_exec_dump(void);

/* trace plate: the .so is the sole owner/writer of .glm_rt_trace.bin
   (sticky 256-byte mmap, CWD-relative — plate.py contract unchanged);
   anonymous pokes (exec tag 0xFF) serve foreign C companions */
void    vx_trace_poke(uint8_t slot);
void    vx_trace_poke_exec(int32_t exec_id, uint8_t slot);
uint8_t vx_trace_fired(uint8_t slot);

/* chronology ring (in-memory, relaxed MPSC, wraps at VX_TRACE_RING_CAP):
   one u32 per poke, (exec_id << 8) | slot — phase-2 file flush seam */
uint64_t vx_trace_event_count(void);
uint32_t vx_trace_event_get(uint64_t seq);

/* --- glm coroutine layer (glm-owned): the coroutine.* parody ------------
   A glm "coroutine" is a compiled .so module running its glm_exec
   PREEMPTIVELY on its own OS pthread; coroutine.yield streams RingPackets
   to the spawning host thread's coroutine.resume over this library's
   lock-free ring (slot i owns ring lane i). The substrate never touches a
   GlmTable: initial inputs ride the LWW in_* cells, and the worker's args
   table is built AND freed inside the thread by the module's own runtime. */

#define VX_CORO_MAX VX_MAX_WINDOWS   /* one ring lane per coroutine */

#define VX_CORO_EMPTY   0u
#define VX_CORO_CREATED 1u   /* context ready, thread not started */
#define VX_CORO_RUNNING 2u   /* pthread live (or finished, pre-join) */
#define VX_CORO_DEAD    3u   /* joined, slot recyclable */

vmath_thread_t vx_thread_start(void* (*func)(void*), void* arg);
void           vx_thread_join(vmath_thread_t thread);

int32_t  vx_coro_create(void* lib);                       /* -> id or -1 */
void     vx_coro_send(int32_t id, uint64_t a, uint64_t b, uint64_t c);
int32_t  vx_coro_start(int32_t id);                       /* idempotent */
int64_t  vx_coro_pull(int32_t id);                        /* blocking consume */
int64_t  vx_coro_yield(uint64_t value);                   /* producer publish */
uint32_t vx_coro_status(int32_t id);                      /* state word */
void     vx_coro_join(int32_t id);                        /* wait + join */
void     vx_coro_quiesce(void);                           /* exit-report pre-pass */

/* str_pool.c — the process-canonical string pool (the third stateful
   layer: trace plate, exec registry, strings). Layout contract, frozen:
     allocation: [8 bytes: i64 key] [N bytes: UTF-8] [1 byte: 0x00]
     handle:     pointer to the UTF-8 bytes — the canonical *const u8
     key:        INT64_MIN | (fnv1a_64(bytes) & 0x3FFF_FFFF_FFFF_FFFF)
   The key derive is a cross-module ABI contract; src/rt.rs and the
   backend's constant folder must stay byte-identical to str_pool.c.
   Allocator rule: the substrate is the sole allocator of interned
   strings and they are immortal — module boundaries cannot split an
   allocation. vx_str_register interns COPIES of .rodata literals and
   overwrites the caller's (writable) strtab slots with canonical
   prefixed pointers, so no unprefixed static string ever masquerades
   as a pool handle. */
const uint8_t* vx_str_intern(const uint8_t* s, size_t len);
void           vx_str_register(const uint8_t** strtab, int64_t n);

#ifdef __cplusplus
}
#endif

#endif
