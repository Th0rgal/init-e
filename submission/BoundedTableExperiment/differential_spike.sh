#!/usr/bin/env bash
# Linked differential test: compile the isolated PNK candidate to an ELF, run
# it on Spike, and compare the returned checksum with the Python semantic model.
#
#   N=200 ./differential_spike.sh          # quick
#   N=5000 ./differential_spike.sh        # growth/delete/truncate scaling
#
# Requires tools/spike/spike_run (build once with SPIKE_SRC=<riscv-isa-sim>).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
N="${N:-200}"
PHASE="${PHASE:-2}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
SPIKE_RUN="${SPIKE_RUN:-$ROOT/tools/spike/spike_run}"
[[ -x "$SPIKE_RUN" ]] || {
  echo "missing $SPIKE_RUN; run: SPIKE_SRC=<riscv-isa-sim> $ROOT/tools/spike/build.sh" >&2
  exit 1
}
[[ $((N % 20)) -eq 0 ]] || { echo "N must be a multiple of 20" >&2; exit 1; }
[[ "$PHASE" =~ ^[012]$ ]] || { echo "PHASE must be 0, 1, or 2" >&2; exit 1; }
DELETE_LOOP=""
TRUNCATE=""
if ((PHASE >= 1)); then
  DELETE_LOOP=$(cat <<LOOP
  var j = 0;
  while j < $((N / 5)) {
    i = j * 5;
    ps_key(buf, i);
    htab_del(t, buf);
    j = j + 1;
  }
LOOP
)
fi
if ((PHASE >= 2)); then
  TRUNCATE="  htab_truncate(t, $((N / 4)));"
fi

cat > "$TMP/test.pnk" <<PNK
#include "config.h"
#include "types.h"
#include "lib/mem.pnk"
#include "$ROOT/submission/BoundedTableExperiment/htab_patricia.pnk"

fun 1 ps_key(1 buf, 1 i) {
  memzero(buf, 20);
  st buf, i;
  st buf + 8, i * 3;
  return 0;
}

fun 1 main() {
  mem_init();
  var 1 t = htab_new(20, 8);
  var 1 buf = alloc(20);
  var i = 0;
  while i < $N {
    ps_key(buf, i);
    htab_set(t, buf, i + 1000);
    i = i + 1;
  }
$DELETE_LOOP
  $TRUNCATE
  var sum = 0;
  var n = htab_count(t);
  i = 0;
  while i < n {
    var {1,1,1} it = htab_item(t, i);
    sum = sum + it.2;
    i = i + 1;
  }
  st 2688614400, sum + n;
  return sum + n;
}
PNK

"$ROOT/guest/build.sh" "$TMP/test.pnk" "$TMP/test.elf" >/dev/null 2>"$TMP/build.err" || {
  cat "$TMP/build.err" >&2; exit 1
}
: > "$TMP/empty.bin"
"$SPIKE_RUN" "$TMP/test.elf" "$TMP/empty.bin" "$TMP/out.bin" 2>"$TMP/spike.err" || {
  cat "$TMP/spike.err" >&2; exit 1
}
cat "$TMP/spike.err"
PYTHONPATH="$ROOT/submission/BoundedTableExperiment" N="$N" PHASE="$PHASE" python3 - "$TMP/out.bin" <<'PY'
import os, sys
from prototype import Patricia
N = int(os.environ['N'])
PHASE = int(os.environ['PHASE'])
p = Patricia(20, 8)
def key(i):
    return i.to_bytes(8, 'little') + ((i * 3) % (1 << 64)).to_bytes(8, 'little') + b'\0' * 4
for i in range(N):
    p.set(key(i), i + 1000)
if PHASE >= 1:
    for j in range(N // 5):
        p.delete(key(j * 5))
if PHASE >= 2:
    p.truncate(N // 4)
expected = sum(v for _, v in p.items()) + len(p.order)
out = open(sys.argv[1], 'rb').read()
got = int.from_bytes(out[:8], 'little')
print(f"N={N} expected={expected} spike={got} steps_ok={got == expected}")
if got != expected:
    raise SystemExit(1)
PY
