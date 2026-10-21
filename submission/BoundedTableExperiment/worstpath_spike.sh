#!/usr/bin/env bash
# Worst-depth path test: keys with a single set bit at positions 0..8*KL-1.
# Inserting them in MSB-first order forces a deep Patricia spine, so repeated
# lookups exercise the 8*key_len deterministic bound rather than a shallow
# random tree.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
KL="${KL:-20}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
SPIKE_RUN="${SPIKE_RUN:-$ROOT/tools/spike/spike_run}"
[[ -x "$SPIKE_RUN" ]] || { echo "missing $SPIKE_RUN" >&2; exit 1; }
BITS=$((8 * KL))
cat > "$TMP/test.pnk" <<PNK
#include "config.h"
#include "types.h"
#include "lib/mem.pnk"
#include "$ROOT/submission/BoundedTableExperiment/htab_patricia.pnk"
fun 1 ps_bitkey(1 buf, 1 j) {
  memzero(buf, $KL);
  var byte = j >> 3;
  var mask = 128 >> (j & 7);
  st8 buf + byte, mask;
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
  while r < 100 {
    i = 0;
    while i < $BITS {
      ps_bitkey(buf, i);
      var {1,1} g = htab_get(t, buf);
      if g.0 == 0 { sum = sum + 1000000000; }
      else { sum = sum + g.1; }
      i = i + 1;
    }
    r = r + 1;
  }
  var n = htab_count(t);
  st 2688614400, sum + n;
  return sum + n;
}
PNK
"$ROOT/guest/build.sh" "$TMP/test.pnk" "$TMP/test.elf" >/dev/null 2>"$TMP/build.err" || { cat "$TMP/build.err" >&2; exit 1; }
: > "$TMP/empty.bin"
"$SPIKE_RUN" "$TMP/test.elf" "$TMP/empty.bin" "$TMP/out.bin" 2>"$TMP/spike.err" || { cat "$TMP/spike.err" >&2; exit 1; }
cat "$TMP/spike.err"
PYTHONPATH="$ROOT/submission/BoundedTableExperiment" KL="$KL" python3 - "$TMP/out.bin" <<'PY'
import os, sys
from prototype import Patricia
KL = int(os.environ['KL']); BITS = 8 * KL
p = Patricia(KL, 8)
def key(j):
    b = bytearray(KL); b[j >> 3] = 128 >> (j & 7); return bytes(b)
for j in range(BITS):
    p.set(key(j), j + 7)
s = 0
for _ in range(100):
    for j in range(BITS):
        s += p.get(key(j), 1000000000)
expected = s + BITS
got = int.from_bytes(open(sys.argv[1], 'rb').read()[:8], 'little')
print(f"worstpath KL={KL} keys={BITS} model_max_visits={p.max_visits} expected={expected} spike={got} ok={got == expected}")
if got != expected:
    raise SystemExit(1)
PY
