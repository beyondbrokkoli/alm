/* async/mailbox.c — vendored from demo_engine/host/ipc/mailbox.c
   (verbatim init loop; MAX_WINDOWS -> VX_MAX_WINDOWS) */

#include "state_types.c"

EXPORT void vx_init_mailbox(void) {
    atomic_init(&g_engine.mailbox.ready_index,  0);
    atomic_init(&g_engine.mailbox.is_running,   1);
    atomic_init(&g_engine.mailbox.lua_finished,  0);
    atomic_init(&g_engine.mailbox.active_window, 0);

    for (int i = 0; i < VX_MAX_WINDOWS; i++) {
        atomic_init(&g_engine.mailbox.tenants[i].vk_instance,    NULL);
        atomic_init(&g_engine.mailbox.tenants[i].vk_surface,     NULL);
        atomic_init(&g_engine.mailbox.tenants[i].glfw_cmd,       OS_CMD_IDLE);
        atomic_init(&g_engine.mailbox.tenants[i].render_cmd,     RND_CMD_IDLE);
        atomic_init(&g_engine.mailbox.tenants[i].glfw_arg_w,     0);
        atomic_init(&g_engine.mailbox.tenants[i].glfw_arg_h,     0);

        for (int k = 0; k < 512; k++) {
            atomic_init(&g_engine.mailbox.tenants[i].keys[k], 0);
        }

        atomic_init(&g_engine.mailbox.tenants[i].mouse_dx,       0.0f);
        atomic_init(&g_engine.mailbox.tenants[i].mouse_dy,       0.0f);
        atomic_init(&g_engine.mailbox.tenants[i].mouse_x,        0.0f);
        atomic_init(&g_engine.mailbox.tenants[i].mouse_y,        0.0f);
        atomic_init(&g_engine.mailbox.tenants[i].click_x,        -1.0f);
        atomic_init(&g_engine.mailbox.tenants[i].click_y,        -1.0f);

        for (int b = 0; b < 8; b++) {
            atomic_init(&g_engine.mailbox.tenants[i].mouse_btns[b], 0);
        }

        atomic_init(&g_engine.mailbox.tenants[i].mouse_captured, 0);
        atomic_init(&g_engine.mailbox.tenants[i].window_resized, 0);
        atomic_init(&g_engine.mailbox.tenants[i].win_w,          1280);
        atomic_init(&g_engine.mailbox.tenants[i].win_h,          720);
    }

    atomic_init(&g_ring.locked_mask, 0);
    for (int i = 0; i < VX_MAX_WINDOWS; i++) {
        atomic_init(&g_ring.ready_idx[i], -1);
        atomic_init(&g_ring.local_read[i], -1);
        for (int f = 0; f < 10; f++) {
            g_ring.active_ring_slots[i][f] = -1;
        }
    }
}
