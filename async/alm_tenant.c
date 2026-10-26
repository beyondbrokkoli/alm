/* async/alm_tenant.c (alm-owned, not engine-vendored): the
   multi-exec tenant registry + the sole-owner trace plate.

   Because this file lives in the ONE shared object the dynamic loader
   guarantees per process, it can make single-writer promises no
   per-artifact alm_rt copy ever could:
     - .alm_rt_trace.bin is opened/mapped exactly once per process (CAS
       once-guard); every poke from every alm artifact and foreign C
       companion lands on the same MAP_SHARED inode — nobody else
       creates the file, so nobody needs to detect an existing mapping.
     - the exit-time leak report is installed once (atexit) and walks
       every registered exec's census mirror, so a leak names the module
       that leaked instead of whichever runtime copy happened to notice.
   alm_rt copies keep no process-wide trace/leak state of their own —
   just the exec_id handle vx_exec_register handed them. */

#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#include "sys_sync.h"
#include "alm_async.h"
#include "state_types.c"

/* once-guard for the whole substrate: 0 = uninitialized, 1 = init in
   flight (the CAS winner), 2 = ready. Every public entry point calls
   ensure_init(); the ELF constructor makes load-time init the norm. */
static _Atomic int g_async_init = 0;

static void ensure_init(void) {
    if (L_R(g_async_init) == 2) return;
    int expected = 0;
    if (CXS(g_async_init, expected, 1)) {
        vx_init_mailbox();
        atomic_init(&g_trace.event_seq, 0);
        atomic_init(&g_trace.plate_init, 0);
        atomic_init(&g_trace.atexit_installed, 0);
        g_trace.plate_map = NULL;
        for (int i = 0; i < VX_TRACE_RING_CAP; i++) {
            g_trace.event_ring[i] = VX_TRACE_EVENT_NONE;
        }
        for (int i = 0; i < VX_EXEC_MAX; i++) {
            atomic_init(&g_execs.slots[i].state, VX_EXEC_EMPTY);
            atomic_init(&g_execs.slots[i].flags, 0);
            atomic_init(&g_execs.slots[i].census_live, 0);
            atomic_init(&g_execs.slots[i].census_total, 0);
            g_execs.slots[i].name[0] = '\0';
        }
        atomic_init(&g_coros.shutdown, 0);
        for (int i = 0; i < VX_CORO_MAX; i++) {
            atomic_init(&g_coros.slots[i].state, VX_CORO_EMPTY);
            atomic_init(&g_coros.slots[i].thread_done, 0);
            atomic_init(&g_coros.slots[i].joined, 0);
            atomic_init(&g_coros.slots[i].in_a, 0);
            atomic_init(&g_coros.slots[i].in_b, 0);
            atomic_init(&g_coros.slots[i].in_c, 0);
            atomic_init(&g_coros.slots[i].yield_seq, 0);
        }
        S(g_async_init, 2);
    } else {
        int spin = 0;
        while (L(g_async_init) != 2) vx_spin_wait(&spin);
    }
}

/* the substrate's init point for sibling translation units (alm_coro.c):
 * public, idempotent, cheap after the first call */
EXPORT void vx_async_ready(void) {
    ensure_init();
}

__attribute__((constructor))
static void alm_async_ctor(void) {
    ensure_init();
}

/* ---- the exit report: ONE handler per process, every exec accounted --- */

static void exit_report(void) {
    /* join every live coroutine thread FIRST — a worker spinning on a
     * full ring abandons its yield once shutdown is set, so the census
     * walk below reads final, race-free numbers */
    vx_coro_quiesce();
    if (getenv("ALM_RT_DUMP")) {
        vx_exec_dump();
    }
    int leaked_any = 0;
    for (int i = 0; i < VX_EXEC_MAX; i++) {
        ExecSlot* s = &g_execs.slots[i];
        if (L(s->state) == VX_EXEC_EMPTY) continue;
        int64_t live = L_R(s->census_live);
        if (live > 0) {
            leaked_any = 1;
            fprintf(stderr,
                    "ALM_TRACE: slot 90 — leak at exit (module %s, "
                    "sys_alloc_count() == %lld)\n",
                    s->name, (long long)live);
        }
    }
    if (leaked_any) {
        vx_trace_poke(VX_TRACE_SLOT_LEAK);
    }
}

static void install_exit_report(void) {
    int expected = 0;
    if (CXS(g_trace.atexit_installed, expected, 1)) {
        atexit(exit_report);
    }
}

/* ---- exec registry ----------------------------------------------------- */

EXPORT int32_t vx_exec_register(const char* name, uint32_t flags) {
    ensure_init();
    for (int i = 0; i < VX_EXEC_MAX; i++) {
        _Atomic uint32_t* st = &g_execs.slots[i].state;
        uint32_t expected = VX_EXEC_EMPTY;
        if (CXS(*st, expected, VX_EXEC_BOOTING)) {
            /* slot won: fill the flat payload under BOOTING, publish with
             * RUNNING (release) so name/flags/census readers pair with it */
            ExecSlot* s = &g_execs.slots[i];
            const char* src = name ? name : "?";
            size_t n = 0;
            for (; n < VX_EXEC_NAME_MAX - 1 && src[n] != '\0'; n++) {
                s->name[n] = src[n];
            }
            s->name[n] = '\0';
            S_R(s->flags, flags);
            S_R(s->census_live, 0);
            S_R(s->census_total, 0);
            S(*st, VX_EXEC_RUNNING);
            install_exit_report();
            return (int32_t)i;
        }
    }
    return -1; /* registry full: the caller degrades honestly — rt.rs keeps
                * exec_id -1, pokes ride the anonymous 0xFF event tag,
                * census mirrors skip (probe_tenant pins the distinct -1) */
}

EXPORT const char* vx_exec_name(int32_t id) {
    if (id < 0 || id >= VX_EXEC_MAX) return "";
    if (L(g_execs.slots[id].state) == VX_EXEC_EMPTY) return "";
    return g_execs.slots[id].name;
}

EXPORT uint32_t vx_exec_state_get(int32_t id) {
    if (id < 0 || id >= VX_EXEC_MAX) return VX_EXEC_EMPTY;
    return L(g_execs.slots[id].state);
}

EXPORT void vx_exec_state_set(int32_t id, uint32_t state) {
    if (id < 0 || id >= VX_EXEC_MAX) return;
    if (state < VX_EXEC_BOOTING || state > VX_EXEC_FAILED) return;
    S(g_execs.slots[id].state, state);
}

EXPORT uint32_t vx_exec_flags_get(int32_t id) {
    if (id < 0 || id >= VX_EXEC_MAX) return 0;
    return L_R(g_execs.slots[id].flags);
}

EXPORT void vx_exec_census_set(int32_t id, int64_t live, int64_t total) {
    if (id < 0 || id >= VX_EXEC_MAX) return;
    S_R(g_execs.slots[id].census_live, live);
    S_R(g_execs.slots[id].census_total, total);
}

EXPORT int32_t vx_exec_count(void) {
    ensure_init();
    int32_t n = 0;
    for (int i = 0; i < VX_EXEC_MAX; i++) {
        if (L(g_execs.slots[i].state) != VX_EXEC_EMPTY) n++;
    }
    return n;
}

EXPORT void vx_exec_dump(void) {
    ensure_init();
    static const char* words[] = {
        "EMPTY", "BOOTING", "RUNNING", "FINISHED", "FAILED",
    };
    fprintf(stderr, "--- ALM EXEC REGISTRY (%d registered) ---\n",
            (int)vx_exec_count());
    for (int i = 0; i < VX_EXEC_MAX; i++) {
        uint32_t st = L(g_execs.slots[i].state);
        if (st == VX_EXEC_EMPTY) continue;
        const char* w = (st <= VX_EXEC_FAILED) ? words[st] : "?";
        fprintf(stderr,
                "  exec[%d] %-24s state=%-8s flags=0x%x live=%lld total=%lld\n",
                i, g_execs.slots[i].name, w, L_R(g_execs.slots[i].flags),
                (long long)L_R(g_execs.slots[i].census_live),
                (long long)L_R(g_execs.slots[i].census_total));
    }
}

/* ---- the trace plate: sole owner of .alm_rt_trace.bin ------------------ */

static uint8_t* plate_map_acquire(void) {
    if (L(g_trace.plate_init) == 2) return g_trace.plate_map;
    int expected = 0;
    if (CXS(g_trace.plate_init, expected, 1)) {
        uint8_t* map = NULL;
        const char* file = ".alm_rt_trace.bin";
        /* anti-stale: this .so is one per process, so a first-init here
         * means a fresh process — remove any leftover plate, then create.
         * The file stays linked so plate.py can read it after exit. */
        unlink(file);
        int fd = open(file, O_RDWR | O_CREAT, 0644);
        if (fd >= 0) {
            if (ftruncate(fd, (off_t)VX_TRACE_SLOTS) == 0) {
                void* p = mmap(NULL, VX_TRACE_SLOTS, PROT_READ | PROT_WRITE,
                               MAP_SHARED, fd, 0);
                if (p != MAP_FAILED) map = (uint8_t*)p;
            }
            close(fd);
        }
        g_trace.plate_map = map; /* NULL on failure: pokes become no-ops */
        S(g_trace.plate_init, 2);
        return map;
    }
    int spin = 0;
    while (L(g_trace.plate_init) != 2) vx_spin_wait(&spin);
    return g_trace.plate_map;
}

EXPORT void vx_trace_poke_exec(int32_t exec_id, uint8_t slot) {
    ensure_init();
    uint8_t* map = plate_map_acquire();
    if (map != NULL) {
        map[slot] = 1; /* sticky byte on the shared inode (benign race) */
    }
    uint32_t tag = ((exec_id < 0) || (exec_id >= VX_EXEC_MAX))
                       ? 0xFFu
                       : ((uint32_t)exec_id & 0xFFu);
    uint64_t seq = atomic_fetch_add_explicit(&g_trace.event_seq, 1,
                                             memory_order_relaxed);
    g_trace.event_ring[seq % VX_TRACE_RING_CAP] = (tag << 8) | slot;
}

EXPORT void vx_trace_poke(uint8_t slot) {
    vx_trace_poke_exec(-1, slot);
}

EXPORT uint8_t vx_trace_fired(uint8_t slot) {
    ensure_init();
    uint8_t* map = plate_map_acquire();
    return (map != NULL) ? map[slot] : 0;
}

EXPORT uint64_t vx_trace_event_count(void) {
    ensure_init();
    return L_R(g_trace.event_seq);
}

EXPORT uint32_t vx_trace_event_get(uint64_t seq) {
    ensure_init();
    if (seq >= L_R(g_trace.event_seq)) return VX_TRACE_EVENT_NONE;
    return g_trace.event_ring[seq % VX_TRACE_RING_CAP];
}
