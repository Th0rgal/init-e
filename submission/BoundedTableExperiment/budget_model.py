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

def max_entries(budget, depth, bsearch_steps, dup_frac):
    per = dup_frac * entry_cost(depth, bsearch_steps, False) + \
          (1 - dup_frac) * entry_cost(depth, bsearch_steps, True)
    return budget / per

def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 33_550_000
    key_len = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    input_bytes = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    # Optional: fixed number of distinct live keys.  A Patricia tree with K
    # leaves has average depth at most min(8*key_len, K-1) (comb), so total
    # descent work scales with the *distinct* count, not the operation count.
    fixed_k = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    budget = int(sys.argv[5]) if len(sys.argv) > 5 else 200_000_000_000
    # A distinct key consumes at least key_len input bytes; a fixed key length
    # also gives at most 2^(8*key_len) distinct keys.
    distinct = n
    if input_bytes:
        distinct = min(distinct, input_bytes // key_len)
    distinct = min(distinct, 1 << (8 * key_len))
    max_depth = 8 * key_len
    if fixed_k:
        avg_depth = max(1, min(max_depth, fixed_k - 1))
        b = max(1, math.ceil(math.log2(avg_depth + 1)))
        fresh = min(fixed_k, distinct)
        total = fresh * entry_cost(avg_depth, b, True) + (n - fresh) * entry_cost(avg_depth, b, False)
        print(json.dumps({"prices": P, "n": n, "key_len": key_len, "K": fixed_k,
                          "avg_depth_bound": avg_depth, "total": total,
                          "per_entry": total / n}, indent=2))
        return
    if len(sys.argv) > 6 and sys.argv[6] == "max":
        rows = []
        for depth in (1, 2, 4, 8, 16, 25):
            b = max(1, math.ceil(math.log2(depth + 1)))
            rows.append({"depth": depth, "budget": budget,
                         "max_entries": {str(d): max_entries(budget, depth, b, d)
                                         for d in (0.0, 0.9, 0.99, 0.999)}})
        print(json.dumps({"prices": P, "rows": rows}, indent=2))
        return
    out = []
    for depth in (4, 8, 16, 25, max_depth):
        b = max(1, math.ceil(math.log2(depth + 1)))
        for dup in (0.0, 0.9, 0.99, 0.999):
            fresh = min(int(n * (1 - dup)), distinct); dupn = n - fresh
            total = fresh * entry_cost(depth, b, True) + dupn * entry_cost(depth, b, False)
            out.append({"depth": depth, "dup_frac": dup, "fresh": fresh,
                        "total": total, "per_entry": total / n})
    print(json.dumps({"prices": P, "n": n, "key_len": key_len,
                      "max_depth": max_depth, "distinct_bound": distinct,
                      "rows": out}, indent=2))

if __name__ == "__main__":
    main()
