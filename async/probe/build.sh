#!/usr/bin/env bash
# async/probe/build.sh — compile the vendored C11 async core into ONE shared
# object, then build the Rust probes against it (DT_NEEDED + $ORIGIN rpath,
# so they run from any CWD). Produces, next to this script:
#   libglm_async.so  probe (3+1 discipline)  probe_1lane (regression canary)
#   probe_tenant (glm exec registry + trace plate layer)
#   probe_backpressure (deterministic full-ring block/resume proof)
set -euo pipefail
cd "$(dirname "$0")"

CC=${CC:-clang}

"$CC" -shared -fPIC -O2 -Wall -Wextra -std=gnu11 -I .. \
    ../sys_sync.c \
    ../state_globals.c \
    ../mailbox.c \
    ../ring_stream.c \
    ../mailbox_accessors.c \
    ../glm_tenant.c \
    ../glm_coro.c \
    -o libglm_async.so -lpthread -ldl

for prog in probe probe_1lane probe_tenant probe_backpressure; do
    rustc --edition 2024 -O "$prog.rs" -o "$prog" \
        -C link-arg=-L. \
        -C link-arg=-lglm_async \
        -C link-arg=-lpthread \
        -C link-arg=-Wl,-rpath,'$ORIGIN'
done

echo "built: libglm_async.so probe probe_1lane probe_tenant probe_backpressure"
