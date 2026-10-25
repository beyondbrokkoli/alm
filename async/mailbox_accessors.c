/* async/mailbox_accessors.c — NEW: function-only accessors so foreign
   runtimes (alm_rt, probes) never need the struct layout; the unity build
   touches g_engine directly, which only C can afford. */

#include "state_types.c"

EXPORT uint8_t vx_key_get(int win_id, int key) {
    if (win_id < 0 || win_id >= VX_MAX_WINDOWS) return 0;
    if (key < 0 || key >= 512) return 0;
    return L_R(g_engine.mailbox.tenants[win_id].keys[key]);
}

EXPORT void vx_key_set(int win_id, int key, uint8_t val) {
    if (win_id < 0 || win_id >= VX_MAX_WINDOWS) return;
    if (key < 0 || key >= 512) return;
    S(g_engine.mailbox.tenants[win_id].keys[key], val);
}

EXPORT float vx_mouse_dx_get(int win_id) {
    if (win_id < 0 || win_id >= VX_MAX_WINDOWS) return 0.0f;
    return L_R(g_engine.mailbox.tenants[win_id].mouse_dx);
}

EXPORT void vx_mouse_delta_set(int win_id, float dx, float dy) {
    if (win_id < 0 || win_id >= VX_MAX_WINDOWS) return;
    S(g_engine.mailbox.tenants[win_id].mouse_dx, dx);
    S(g_engine.mailbox.tenants[win_id].mouse_dy, dy);
}

EXPORT int vx_running_get(void) {
    return L(g_engine.mailbox.is_running);
}

EXPORT void vx_running_set(int running) {
    S(g_engine.mailbox.is_running, running);
}
