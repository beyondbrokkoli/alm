/* async/ring_stream.c — vendored from demo_engine/host/ipc/ring_stream.c
   (trimmed: no vx_stream_init / WSI / busy flags; vx_stream_release is NEW —
    the consumer-side FA the engine does inline in vk_render_loop.c:86;
    vx_stream_next is the consumer gate+advance from vk_render_loop.c:62-76) */

#include "state_types.c"

EXPORT RingPacket* vx_stream_packet(int idx) {
    if (idx < 0 || idx >= VX_RING_SIZE) {
        printf("[FATAL] -1 index requests");
        return NULL;
    }
    return &g_ring.packets[idx];
}

EXPORT int vx_stream_acquire(int win_id) {
    if (win_id < 0 || win_id >= VX_MAX_WINDOWS) return -1;
    int ready  = L(g_ring.ready_idx[win_id]);
    int offset = win_id * 4;
    // FIFO ring: only (ready+1)%4 is ever a valid write; locked here means
    // the ring is full.
    int local_curr = (ready == -1) ? -1 : (ready - offset);
    int next_local = (local_curr + 1) % 4;
    int global_idx = offset + next_local;
    uint32_t bit   = (1u << global_idx);
    uint32_t expected = L(g_ring.locked_mask);

    while ((expected & bit) == 0) {
        if (CWX(g_ring.locked_mask, expected, expected | bit)) return global_idx;
    }
    return -1;
}

EXPORT void vx_stream_commit(int win_id, int idx) {
    if (win_id < 0 || win_id >= VX_MAX_WINDOWS) return;
    atomic_thread_fence(memory_order_release);
    S(g_ring.ready_idx[win_id], idx);
}

EXPORT void vx_stream_release(int win_id, int idx) {
    if (win_id < 0 || win_id >= VX_MAX_WINDOWS) return;
    if (idx < 0 || idx >= VX_RING_SIZE) return;
    FA(g_ring.locked_mask, ~(1u << idx));
}

EXPORT int vx_stream_next(int win_id) {
    if (win_id < 0 || win_id >= VX_MAX_WINDOWS) return -1;
    int ready = L(g_ring.ready_idx[win_id]);
    int local = L(g_ring.local_read[win_id]);
    if (ready == -1 || ready == local) return -1;
    int offset = win_id * 4;
    int new_local = (local == -1)
        ? offset + 0
        : offset + ((local - offset + 1) % 4);
    S(g_ring.local_read[win_id], new_local);
    return new_local;
}

EXPORT void vx_stream_dump(int win_id) {
    printf("--- RING DUMP (win %d) ---\n", win_id);
    printf("ready_idx=%d local_read=%d locked_mask=0x%08x\n",
           L_R(g_ring.ready_idx[win_id]), L_R(g_ring.local_read[win_id]),
           L_R(g_ring.locked_mask));
    for (int i = 0; i < VX_RING_SIZE; i++) {
        printf("  packet[%2d] seq=%llu\n", i,
               (unsigned long long)g_ring.packets[i].seq);
    }
    fflush(stdout);
}
