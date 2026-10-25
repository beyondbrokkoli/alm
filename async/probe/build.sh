#!/usr/bin/env bash
# async/probe/build.sh — compile the vendored C11 async core into ONE shared
# object (the SAME source list as the shipped build.rs, str_pool.c
# included — R10: the probed library must be the shipped one), then build
# the Rust probes against it (DT_NEEDED + $ORIGIN rpath,
# so they run from any CWD). Produces, next to this script:
#   libalm_async.so  probe (3+1 discipline)  probe_1lane (regression canary)
#   probe_tenant (alm exec registry + trace plate layer)
#   probe_backpressure (deterministic full-ring block/resume proof)
#   probe_recycle (R9: slot recycle + distinct exhaustion)
set -euo pipefail
cd "$(dirname "$0")"

CC=${CC:-clang}

"$CC" -shared -fPIC -O2 -Wall -Wextra -std=gnu11 -I .. \
    ../sys_sync.c \
    ../state_globals.c \
    ../mailbox.c \
    ../ring_stream.c \
    ../mailbox_accessors.c \
    ../alm_tenant.c \
    ../alm_coro.c \
    ../str_pool.c \
    -o libalm_async.so -lpthread -ldl

for prog in probe probe_1lane probe_tenant probe_backpressure probe_recycle; do
    rustc --edition 2024 -O "$prog.rs" -o "$prog" \
        -C link-arg=-L. \
        -C link-arg=-lalm_async \
        -C link-arg=-lpthread \
        -C link-arg=-Wl,-rpath,'$ORIGIN'
done

echo "built: libalm_async.so probe probe_1lane probe_tenant probe_backpressure probe_recycle"
