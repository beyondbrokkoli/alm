/* async/state_globals.c — vendored from demo_engine/host/state/state_globals.c
   (trimmed: no Vulkan handles, no transfer ring, no thread handles) */

#include "state_types.c"

EngineState  g_engine;
RenderRing   g_ring;
ExecRegistry g_execs;
TraceState   g_trace;
CoroRegistry g_coros;
