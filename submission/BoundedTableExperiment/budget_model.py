#!/usr/bin/env python3
"""Parameteric source-cost composition for the frozen Patricia candidate.

Prices are optimized (removeDead) per executed loop body from the frontend-only
harness; they are diagnostics, not a checked bound.
"""
import json, math, sys

P = {"find_per_visit": 723, "path_per_visit": 1107, "bsearch_per_step": 592,
     "relocate_per_node": 1203, "grow_per_loop": 1611, "truncate_per_step": 1307,
     "delete_per_visit": 1614}

def entry_cost(depth, bsearch_steps, fresh):
    c = depth * P["path_per_visit"]
    if fresh:
        c += bsearch_steps * P["bsearch_per_step"]
        c += 2 * P["relocate_per_node"]          # <=2 relocated internal nodes / leaf
        c += P["grow_per_loop"]                  # one growth-loop body
    return c

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 33_550_000
    out = []
    for depth in (4, 8, 16, 25):
        b = max(1, math.ceil(math.log2(depth + 1)))
        for dup in (0.0, 0.9, 0.99, 0.999):
            fresh = int(n * (1 - dup)); dupn = n - fresh
            total = fresh * entry_cost(depth, b, True) + dupn * entry_cost(depth, b, False)
            out.append({"depth": depth, "dup_frac": dup, "fresh": fresh,
                        "total": total, "per_entry": total / n})
    print(json.dumps({"prices": P, "n": n, "rows": out}, indent=2))

if __name__ == "__main__":
    main()
