/* async/sys_sync.c — vendored from demo_engine/host/ipc/sys_sync.c
   (macro block split into sys_sync.h; vx_spin_wait un-static'd for export) */

#include "sys_sync.h"

EXPORT void vx_spin_wait(int* spin_count) {
    if (*spin_count < 1000) {
        _mm_pause();
    } else if (*spin_count < 2000) {
        #if defined(_WIN32)
            SwitchToThread();
        #else
            sched_yield();
        #endif
    } else {
        SLEEP_MS(1);
    }
    (*spin_count)++;
}

/* vendored verbatim from demo_engine/host/threading/thread_pool.c (the
   whole 11-line file): thread lifecycle is the embedder's job — glm_coro.c
   is the embedder now. Un-static'd + EXPORT for cross-DSO callers. */

EXPORT vmath_thread_t vx_thread_start(void* (*func)(void*), void* arg) {
    pthread_t thread;
    pthread_create(&thread, NULL, func, arg);
    return thread;
}

EXPORT void vx_thread_join(vmath_thread_t thread) {
    pthread_join(thread, NULL);
}
