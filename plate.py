#!/usr/bin/env python3
"""
[USAGE & CLI]
  python3 plate.py                      Decode default (./.alm_trace.bin)
  python3 plate.py <plate.bin>          Decode explicit plate
  python3 plate.py <good.bin> <bad.bin> Event-sequence diff (baseline, suspect)
  python3 plate.py -s <signals.txt> ... Override SSOT registry path

[DEFAULTS]
  Plate     : ./.alm_trace.bin
  Registry  : ./trace_signals.txt (resolved relative to script directory)

[DECODER FORMAT DISPATCH]
  1. Compiler Chronology Plate (`.alm_trace.bin`)
     Offset 0..4   : fired (u32 LE)    — total events emitted (writer sequence)
     Offset 4..8   : capacity (u32 LE) — ring buffer size (C)
     Offset 8..8+C : ring (u8[C])      — slot bytes in fire order (wraps at C)

  2. Runtime Sidecar Plate (`.alm_rt_trace.bin`)
     Detection     : Input size == 256 bytes
     Semantics     : Sticky boolean array (u8[256]) from target process.
     Output        : List of slots that fired at least once.

[RESOLUTION & FALLBACK]
  Mapped    : <slot> -> (NAME, owner, meaning) via SSOT registry.
  Unmapped  : Slot byte missing from SSOT decodes as `SLOT_<n>`.
"""

import argparse
import sys
from pathlib import Path

SIDECAR_LEN = 256  # .alm_rt_trace.bin: one sticky byte per slot
HDR_LEN = 8

DEFAULT_PLATE = ".alm_trace.bin"


def load_signals(path: Path):
    """Parse trace_signals.txt: one `slot NAME owner meaning` per line."""
    signals = {}
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split(None, 3)
        if len(fields) != 4:
            sys.exit(f"{path}:{lineno}: expected `<slot> <NAME> <owner> <meaning>`: {line}")
        slot_s, name, owner, meaning = fields
        if not slot_s.isdigit() or int(slot_s) > 255:
            sys.exit(f"{path}:{lineno}: slot `{slot_s}` outside 0..=255")
        slot = int(slot_s)
        if slot in signals:
            sys.exit(f"{path}:{lineno}: slot {slot} double-booked ({signals[slot][0]} vs {name})")
        signals[slot] = (name, owner, meaning)
    if not signals:
        sys.exit(f"{path}: no signals declared")
    return signals


def signal_name(slot, signals):
    return signals[slot][0] if slot in signals else f"SLOT_{slot}"


def load_plate(path: Path):
    if not path.exists():
        sys.exit(f"no plate at {path} — compile something first")
    return path.read_bytes()


def decode_ring(data, path):
    """(events in fire order, count of overwritten oldest events)."""
    if len(data) < HDR_LEN:
        if len(data) == SIDECAR_LEN:
            sys.exit(f"{path} is a runtime sidecar (sticky-only), not a chronology plate")
        print(f"note: {path} is {len(data)} bytes, no chronology header", file=sys.stderr)
        return [], 0
    fired = int.from_bytes(data[0:4], "little")
    capacity = int.from_bytes(data[4:8], "little")
    if fired == 0:
        return [], 0
    if capacity == 0:
        sys.exit(f"{path}: {fired} events but capacity 0 — corrupt plate")
    dropped = max(0, fired - capacity)
    valid = min(fired, capacity)
    start = dropped % capacity
    events = []
    for i in range(valid):
        off = HDR_LEN + ((start + i) % capacity)
        if off >= len(data):  # truncated file: stop at what is there
            break
        events.append(data[off])
    return events, dropped


def decode_sidecar(data):
    """Runtime sidecar: slots whose sticky byte is set."""
    return [n for n in range(len(data)) if data[n]]


# single-plate mode

def run_single(plate_path, signals):
    data = load_plate(plate_path)

    if len(data) == SIDECAR_LEN:
        fired = decode_sidecar(data)
        print(f"plate:   {plate_path} (runtime sidecar — sticky booleans, no order)")
        print(f"fired at least once ({len(fired)}):")
        print("  " + (" ".join(f"{n}:{signal_name(n, signals)}" for n in fired)
                      if fired else "(nothing)"))
        return

    events, dropped = decode_ring(data, plate_path)
    print(f"plate:   {plate_path} ({len(data)} bytes)")
    print(f"signals: {len(signals)} slots in the SSOT")
    print(f"\n== Event Chronology ({len(events) + dropped} events this run) ==")
    if dropped:
        print(f"  ... [oldest {dropped} overwritten — the {len(events)} below are "
              "the newest] ...")
    if not events:
        print("  (nothing fired — no compile ran, or the plate is zeroed)")
    for i, slot in enumerate(events):
        print(f"  {i + 1:04d} : {signal_name(slot, signals)}")


# diff mode

def tail_tokens(events, signals, limit=30):
    shown = " ".join(signal_name(s, signals) for s in events[:limit])
    more = f" … (+{len(events) - limit} more)" if len(events) > limit else ""
    return shown + more if events else "(end of plate)"


def run_diff(good_path, bad_path, signals):
    good, bad = load_plate(good_path), load_plate(bad_path)
    print(f"good:    {good_path}  (baseline)")
    print(f"bad:     {bad_path}  (suspect)")

    if good == bad:
        print("\n(plates are byte-identical — the contract's expectation for "
              "two runs of the same case)")
        return

    if len(good) == SIDECAR_LEN or len(bad) == SIDECAR_LEN:
        g, b = decode_sidecar(good), decode_sidecar(bad)
        only_g = [n for n in g if n not in b]
        only_b = [n for n in b if n not in g]
        print(f"\n== Fired-set diff (sidecar plates carry no order) ==")
        print("  only in good: " + (" ".join(signal_name(n, signals) for n in only_g)
                                    or "(none)"))
        print("  only in bad:  " + (" ".join(signal_name(n, signals) for n in only_b)
                                    or "(none)"))
        return

    g_events, g_dropped = decode_ring(good, good_path)
    b_events, b_dropped = decode_ring(bad, bad_path)
    if g_dropped or b_dropped:
        print(f"\nnote: ring overflow — oldest {g_dropped} (good) / {b_dropped} (bad) "
              "events were overwritten; the sequences start mid-run and may "
              "not align event-for-event")

    print(f"\n== Chronology diff (good {len(g_events)} events, bad {len(b_events)}) ==")
    prefix = 0
    for g, b in zip(g_events, b_events):
        if g != b:
            break
        prefix += 1

    if prefix == len(g_events) == len(b_events):
        print("  (identical event sequences — the trailing plate bytes differ, "
              "but nothing the ring records does)")
        return

    print(f"  common prefix: {prefix} events")
    if prefix < len(g_events) or prefix < len(b_events):
        g_next = signal_name(g_events[prefix], signals) if prefix < len(g_events) else "(end)"
        b_next = signal_name(b_events[prefix], signals) if prefix < len(b_events) else "(end)"
        print(f"  first divergence at event {prefix + 1}: good {g_next}, bad {b_next}")
    print(f"  good continues: {tail_tokens(g_events[prefix:], signals)}")
    print(f"  bad continues:  {tail_tokens(b_events[prefix:], signals)}")


def main():
    # Piping into head/less closes stdout early; die quietly like a
    # shell utility instead of tracebacking.
    import signal
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)

    ap = argparse.ArgumentParser(
        prog="plate.py",
        description="Decode the .alm_trace.bin event chronology, or diff two "
                    "plates (good.bin bad.bin — baseline first, suspect second).")
    ap.add_argument("plates", nargs="*", metavar="PLATE",
                    help="one plate -> chronology; two plates -> diff")
    ap.add_argument("-s", "--signals", metavar="FILE", type=Path,
                    help="path to trace_signals.txt (default: next to this script)")
    args = ap.parse_args()

    if len(args.plates) > 2:
        ap.error("expected at most: good.bin bad.bin")
    ssot_path = (args.signals if args.signals is not None
                 else Path(__file__).resolve().parent / "trace_signals.txt")
    signals = load_signals(ssot_path)

    if len(args.plates) == 2:
        run_diff(Path(args.plates[0]), Path(args.plates[1]), signals)
    else:
        plate_path = Path(args.plates[0]) if args.plates else Path(DEFAULT_PLATE)
        run_single(plate_path, signals)


if __name__ == "__main__":
    main()
