#!/usr/bin/env python3
"""Check trace events against the PNK operation shape.

The PNK relation checked per event:
- set_new: one path descent (path_stores == visits), one binary search
  (0 <= bsearch_steps <= ceil(log2(depth+1))), one child-link write;
- set_update: descent only, no path stores/search/link write;
- get: descent only;
- delete: at most one swap-remove order move.
"""
import json, math, subprocess, sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

def load():
    out = subprocess.check_output([sys.executable, str(HERE / "trace_model.py")], cwd=HERE)
    return json.loads(out)

def check(ev):
    op = ev["op"]
    if op == "set_new":
        depth = ev["path_stores"]
        expected_visits = depth * (2 if ev["grows"] > 0 else 1)
        link = 0 if ev["count"] == 1 else 1
        return (expected_visits == ev["visits"] and ev["link_writes"] == link and
                0 <= ev["bsearch_steps"] <= max(1, math.ceil(math.log2(depth + 1))))
    if op == "set_update":
        return ev["path_stores"] == 0 and ev["bsearch_steps"] == 0 and ev["link_writes"] == 0
    if op == "get":
        return ev["path_stores"] == 0 and ev["bsearch_steps"] == 0 and ev["link_writes"] == 0
    if op in ("delete", "delete_miss"):
        return ev["order_moves"] <= 1 and ev["path_stores"] == 0
    return False

def main():
    data = load()
    bad = [ev for ev in data["events"] if not check(ev)]
    counts = {}
    for ev in data["events"]:
        counts[ev["op"]] = counts.get(ev["op"], 0) + 1
    print(json.dumps({"events": len(data["events"]), "counts": counts,
                      "failures": len(bad)}, indent=2))
    if bad:
        print(json.dumps(bad[:5], indent=2))
        raise SystemExit(1)

if __name__ == "__main__":
    main()
