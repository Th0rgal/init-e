#!/usr/bin/env python3
"""Emit a concrete per-operation trace for source-cost calibration.

This uses the executable Patricia model and records deltas of every counter the
source-price model needs.  It is a behavior/count trace, not a source-event
trace; the exact preIsel price still multiplies these counts.
"""
import json
from prototype import Patricia

COUNTERS = ("visits", "bit_tests", "key_compares", "compare_bytes",
            "first_diff_bytes", "order_moves", "grows", "copy_moves",
            "path_stores", "bsearch_steps", "link_writes")

def snap(p):
    return {k: getattr(p, k) for k in COUNTERS}

def key(i, kl=20):
    return i.to_bytes(8, 'little') + ((i * 3) % (1 << 64)).to_bytes(8, 'little') + b'\0' * (kl - 16)

def main():
    kl, n = 20, 1000
    p = Patricia(kl, 8)
    events = []
    base = snap(p)
    for i in range(n):
        ok = p.set(key(i, kl), i)
        cur = snap(p)
        events.append({"op": "set_new" if ok else "set_update", "i": i,
                       "cap": p.cap, "count": len(p.order),
                       **{k: cur[k] - base[k] for k in COUNTERS}})
        base = cur
    for i in range(0, n, 3):
        ok = p.delete(key(i, kl))
        cur = snap(p)
        events.append({"op": "delete" if ok else "delete_miss", "i": i,
                       "cap": p.cap, "count": len(p.order),
                       **{k: cur[k] - base[k] for k in COUNTERS}})
        base = cur
    for i in range(0, n, 7):
        p.get(key(i, kl))
        cur = snap(p)
        events.append({"op": "get", "i": i, "cap": p.cap, "count": len(p.order),
                       **{k: cur[k] - base[k] for k in COUNTERS}})
        base = cur
    print(json.dumps({"key_len": kl, "events": events}, separators=(",", ":")))

if __name__ == "__main__":
    main()
