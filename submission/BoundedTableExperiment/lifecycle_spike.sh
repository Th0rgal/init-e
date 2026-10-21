#!/usr/bin/env bash
# Linked lifecycle test: copy / copy_scratch independence, growth with stale
# links, deletion and pool recycling.  The guest computes a boolean status and
# the Python model computes the same expected status.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
SPIKE_RUN="${SPIKE_RUN:-$ROOT/tools/spike/spike_run}"
[[ -x "$SPIKE_RUN" ]] || {
  echo "missing $SPIKE_RUN; run: SPIKE_SRC=<riscv-isa-sim> $ROOT/tools/spike/build.sh" >&2
  exit 1
}
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
  while i < 200 {
    ps_key(buf, i);
    htab_set(t, buf, i);
    i = i + 1;
  }
  var ok = 1;
  /* Deep copy must be independent of the original. */
  var 1 c = htab_copy(t);
  ps_key(buf, 999);
  htab_set(c, buf, 9999);
  ps_key(buf, 0);
  htab_del(c, buf);
  ps_key(buf, 0);
  var {1,1} g0 = htab_get(t, buf);
  ps_key(buf, 999);
  var {1,1} g999 = htab_get(t, buf);
  if g0.0 == 0 { ok = 0; }
  if g999.0 != 0 { ok = 0; }
  ps_key(buf, 0);
  var {1,1} c0 = htab_get(c, buf);
  if c0.0 != 0 { ok = 0; }
  /* Scratch copy must also be independent while its frame is alive. */
  var 1 s = htab_copy_scratch(t);
  ps_key(buf, 1000);
  htab_set(s, buf, 1000);
  var {1,1} ts = htab_get(t, buf);
  var {1,1} ss = htab_get(s, buf);
  if ts.0 != 0 { ok = 0; }
  if ss.0 == 0 { ok = 0; }
  /* Delete/reinsert across the growth boundary; old links must be dead. */
  i = 0;
  while i < 100 {
    ps_key(buf, i);
    htab_del(t, buf);
    i = i + 1;
  }
  i = 200;
  while i < 300 {
    ps_key(buf, i);
    htab_set(t, buf, i);
    i = i + 1;
  }
  i = 0;
  while i < 300 {
    ps_key(buf, i);
    var {1,1} g = htab_get(t, buf);
    if i < 100 {
      if g.0 != 0 { ok = 0; }
    } else {
      if g.0 == 0 { ok = 0; }
    }
    i = i + 1;
  }
  /* Repeated recycling of one leaf through the free list. */
  i = 0;
  while i < 50 {
    ps_key(buf, 150);
    htab_del(t, buf);
    ps_key(buf, 150);
    htab_set(t, buf, 150 + i);
    i = i + 1;
  }
  ps_key(buf, 150);
  var {1,1} final = htab_get(t, buf);
  if final.0 == 0 { ok = 0; }
  var n = htab_count(t);
  st 2688614400, ok * 1000000 + n;
  return ok * 1000000 + n;
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
python3 - "$TMP/out.bin" <<'PY'
import sys
out = open(sys.argv[1], 'rb').read()
got = int.from_bytes(out[:8], 'little')
# status bit * 1e6 + count; expected count is 200
expected = 1000000 + 200
print(f"lifecycle expected={expected} spike={got} ok={got == expected}")
if got != expected:
    raise SystemExit(1)
PY
