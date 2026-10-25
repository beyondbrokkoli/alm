/* async/state_types.c — vendored from demo_engine/host/state/state_types.c
   (trimmed: RenderPacket -> RingPacket payload lanes, TransferJob dropped) */

#include <stdint.h>
#include <stdio.h>
#include <stdatomic.h>
#include <stdalign.h>
#include <stddef.h>
#include "sys_sync.h"
#include "alm_async.h"

#define OS_CMD_IDLE          0
#define OS_CMD_BOOT_WINDOW   1
#define OS_CMD_KILL_WINDOW   2

#define RND_CMD_IDLE         0
#define RND_CMD_REBUILD_WSI  1
#define RND_CMD_HALT         2
#define RND_CMD_INJECT_TENANT 3

typedef struct {
    _Atomic(void*)  vk_instance;
    _Atomic(void*)  vk_surface;
    _Atomic int     glfw_cmd;
    _Atomic int     render_cmd;
    _Atomic int     glfw_arg_w;
    _Atomic int     glfw_arg_h;

    _Atomic uint8_t keys[512];

    _Atomic float   mouse_dx;
    _Atomic float   mouse_dy;
    _Atomic float   mouse_x;
    _Atomic float   mouse_y;
    _Atomic int     mouse_captured;
    _Atomic int     window_resized;
    _Atomic int     win_w;
    _Atomic int     win_h;
    _Atomic float   click_x;
    _Atomic float   click_y;
    _Atomic uint8_t mouse_btns[8];

    uint8_t         _pad[48];
} TenantMailbox;

_Static_assert(sizeof(TenantMailbox) == 640, "TenantMailbox must prevent false sharing");

typedef struct {
    alignas(64) _Atomic int ready_index;
    _Atomic int is_running;
    _Atomic int lua_finished;
    _Atomic int active_window;
    alignas(64) TenantMailbox tenants[VX_MAX_WINDOWS];
} IPC_Mailbox;

typedef struct {
    IPC_Mailbox mailbox;
    int render_index;
    int write_index;
} EngineState;

typedef struct {
    alignas(64) RingPacket packets[VX_RING_SIZE];
    alignas(64) _Atomic int  ready_idx[VX_MAX_WINDOWS];
    alignas(64) _Atomic int  local_read[VX_MAX_WINDOWS];
    alignas(64) int          active_ring_slots[VX_MAX_WINDOWS][10];
    alignas(64) _Atomic uint32_t locked_mask;
} RenderRing;

extern EngineState g_engine;
extern RenderRing  g_ring;

/* alm tenant & trace layer (NEW, alm-owned — not engine-vendored):
   ExecSlot is the per-artifact identity + census mirror; TraceState is
   the sole-owner plate mapping plus the in-memory chronology ring. The
   registry is flat fixed-size state — no heap, no strings beyond the
   bounded name — so everything crosses the C ABI as plain values. */

typedef struct {
    alignas(64) _Atomic uint32_t state;    /* VX_EXEC_EMPTY..FAILED */
    _Atomic uint32_t flags;                /* VX_EXEC_F_EXE / VX_EXEC_F_SO */
    _Atomic int64_t  census_live;          /* mirrored live AlmTable count */
    _Atomic int64_t  census_total;         /* mirrored total allocations */
    char             name[VX_EXEC_NAME_MAX]; /* written under BOOTING only */
} ExecSlot;

typedef struct {
    alignas(64) ExecSlot slots[VX_EXEC_MAX];
} ExecRegistry;

typedef struct {
    alignas(64) _Atomic uint64_t event_seq;             /* chronology cursor */
    _Atomic int      plate_init;                        /* 0 -> 1 mapping -> 2 ready */
    _Atomic int      atexit_installed;
    uint8_t*         plate_map;                         /* sole-owner mmap of the plate */
    uint32_t         event_ring[VX_TRACE_RING_CAP];     /* (exec<<8)|slot, wraps */
} TraceState;

/* alm coroutine layer (NEW, alm-owned): a "coroutine" is a compiled .so
   module running its alm_exec on a dedicated OS pthread, streaming
   RingPackets to the spawning host thread over the ring LANE OF THE SAME
   INDEX (slot i owns g_ring tenant i — VX_CORO_MAX == VX_MAX_WINDOWS).
   The slot is flat fixed-size state: the dlopen handle, LWW input cells
   (the marshaled resume table), the yield ordinal, and the thread
   lifecycle flags. No heap, no locks. */

typedef struct {
    alignas(64) _Atomic uint32_t state;    /* VX_CORO_EMPTY..DEAD */
    void*            lib;                  /* dlopen handle, set at create */
    vmath_thread_t   thread;               /* valid while RUNNING */
    _Atomic int32_t  thread_done;          /* wrapper sets 1 before exit */
    _Atomic int32_t  joined;
    _Atomic int32_t  abort;                /* close(): break the producer's
                                              full-ring spin, yields drop */
    _Atomic uint64_t in_a;                 /* marshaled resume inputs (LWW) */
    _Atomic uint64_t in_b;
    _Atomic uint64_t in_c;
    _Atomic uint64_t yield_seq;            /* packet ordinal */
    int32_t          held_idx;             /* consumer's held slot (the 1-lane
                                              floor: caps producer at +3) */
} CoroSlot;

typedef struct {
    alignas(64) CoroSlot     slots[VX_CORO_MAX];
    _Atomic int32_t          shutdown;    /* exit-report break: abandons yields */
} CoroRegistry;

extern EngineState  g_engine;
extern RenderRing   g_ring;
extern ExecRegistry g_execs;
extern TraceState   g_trace;
extern CoroRegistry g_coros;
