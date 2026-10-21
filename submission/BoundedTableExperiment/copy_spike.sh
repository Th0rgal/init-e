#!/usr/bin/env bash
# Measure executed copy cost: N inserts, then COPIES heap copies (or scratch
# copies), with an unchanged final count.  Compare COPIES=0 vs 1.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
N="${N:-5000}"
COPIES="${COPIES:-0}"
SCRATCH="${SCRATCH:-0}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
SPIKE_RUN="${SPIKE_RUN:-$ROOT/tools/spike/spike_run}"
[[ -x "$SPIKE_RUN" ]] || { echo "missing $SPIKE_RUN" >&2; exit 1; }
COPY_CALL="htab_copy(t)"; [ "$SCRATCH" = 1 ] && COPY_CALL="htab_copy_scratch(t)"
cat > "$TMP/test.pnk" <<PNK
#include "config.h"
#include "types.h"
#include "lib/mem.pnk"
#include "$ROOT/submission/BoundedTableExperiment/htab_patricia.pnk"
fun 1 ps_key(1 buf, 1 i) { memzero(buf, 20); st buf, i; st buf + 8, i * 3; return 0; }
fun 1 main() {
  mem_init();
  var 1 t = htab_new(20, 8);
  var 1 buf = alloc(20);
  var i = 0;
  while i < $N { ps_key(buf, i); htab_set(t, buf, i); i = i + 1; }
  var 1 last = 0;
  i = 0;
  while i < $COPIES { last = $COPY_CALL; i = i + 1; }
  var n = htab_count(t);
  var m = 0;
  if last != 0 { m = htab_count(last); }
  st 2688614400, n * 100 + m;
  return n;
}
PNK
"$ROOT/guest/build.sh" "$TMP/test.pnk" "$TMP/test.elf" >/dev/null 2>"$TMP/build.err" || { cat "$TMP/build.err" >&2; exit 1; }
: > "$TMP/empty.bin"
"$SPIKE_RUN" "$TMP/test.elf" "$TMP/empty.bin" "$TMP/out.bin" 2>"$TMP/spike.err" || { cat "$TMP/spike.err" >&2; exit 1; }
cat "$TMP/spike.err"
python3 - "$TMP/out.bin" "$N" <<'PY'
import sys
out = open(sys.argv[1], 'rb').read(); got = int.from_bytes(out[:8], 'little'); n = int(sys.argv[2])
# If a copy exists its count is n; expression is n*100 + (n or 0)
expect_zero = n * 100
expect_copy = n * 100 + n
print(f"copy N={n} got={got} (expected {expect_zero} for 0 copies, {expect_copy} for >=1)")
if got not in (expect_zero, expect_copy):
    raise SystemExit(1)
PY
