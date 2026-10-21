#!/usr/bin/env bash
# Deepest-leaf-only lookup cost.  Builds the single-set-bit spine, then repeats
# exactly one maximum-depth key REPEAT times.  Compare REPEAT=0 and REPEAT>0 to
# get the true per-lookup cost without averaging over shallower spine keys.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
KL="${KL:-32}"; REPEAT="${REPEAT:-0}"
case "$KL" in 20) DEEP=158;; 32) DEEP=254;; 60) DEEP=478;; *) echo "KL must be 20/32/60" >&2; exit 1;; esac
BITS=$((8*KL))
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
SPIKE_RUN="${SPIKE_RUN:-$ROOT/tools/spike/spike_run}"
[[ -x "$SPIKE_RUN" ]] || { echo "missing $SPIKE_RUN" >&2; exit 1; }
cat > "$TMP/test.pnk" <<PNK
#include "config.h"
#include "types.h"
#include "lib/mem.pnk"
#include "$ROOT/submission/BoundedTableExperiment/htab_patricia.pnk"
fun 1 ps_bitkey(1 buf, 1 j) {
  memzero(buf, $KL);
  st8 buf + (j >> 3), 128 >> (j & 7);
  return 0;
}
fun 1 main() {
  mem_init();
  var 1 t = htab_new($KL, 8);
  var 1 buf = alloc($KL);
  var i = 0;
  while i < $BITS { ps_bitkey(buf, i); htab_set(t, buf, i + 7); i = i + 1; }
  var sum = 0;
  var r = 0;
  while r < $REPEAT {
    ps_bitkey(buf, $DEEP);
    var {1,1} g = htab_get(t, buf);
    if g.0 == 0 { sum = sum + 1000000000; } else { sum = sum + g.1; }
    r = r + 1;
  }
  var n = htab_count(t);
  st 2688614400, sum + n;
  return sum;
}
PNK
"$ROOT/guest/build.sh" "$TMP/test.pnk" "$TMP/test.elf" >/dev/null 2>"$TMP/build.err" || { cat "$TMP/build.err" >&2; exit 1; }
: > "$TMP/empty.bin"
"$SPIKE_RUN" "$TMP/test.elf" "$TMP/empty.bin" "$TMP/out.bin" 2>"$TMP/spike.err" || { cat "$TMP/spike.err" >&2; exit 1; }
cat "$TMP/spike.err"
PYTHONPATH="$ROOT/submission/BoundedTableExperiment" KL="$KL" REPEAT="$REPEAT" python3 - "$TMP/out.bin" <<'PY'
import os, sys
from prototype import Patricia
KL=int(os.environ['KL']); R=int(os.environ['REPEAT']); B=8*KL
DEEP={20:158,32:254,60:478}[KL]
p=Patricia(KL,8)
def key(j):
    b=bytearray(KL); b[j>>3]=128>>(j&7); return bytes(b)
for j in range(B): p.set(key(j), j+7)
before=p.visits
s=0
for _ in range(R): s += p.get(key(DEEP), 1000000000)
expected=s+B
got=int.from_bytes(open(sys.argv[1],'rb').read()[:8],'little')
print(f"deepest KL={KL} repeat={R} depth={p.max_visits} model_lookup_visits={p.visits-before} expected={expected} spike={got} ok={got==expected}")
if got!=expected: raise SystemExit(1)
PY
