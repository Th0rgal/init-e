#!/usr/bin/env bash
# Parser/type-check the isolated candidate with Flapjack's Pancake frontend.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cat > "$TMP/test.pnk" <<PNK
#include "config.h"
#include "types.h"
#include "lib/mem.pnk"
#include "$ROOT/submission/BoundedTableExperiment/htab_patricia.pnk"

fun 1 main() {
  mem_init();
  var 1 t = htab_new(32, 8);
  var 1 k = alloc(32);
  st k, 1;
  htab_set(t, k, 7);
  var {1,1} g = htab_get(t, k);
  var {1,1,1} it = htab_item(t, 0);
  htab_del(t, k);
  htab_truncate(t, 0);
  var n = htab_count(t);
  return g.0 + it.0 + n;
}
PNK
cpp -P -w -nostdinc -I "$ROOT/guest/src" -x c "$TMP/test.pnk" \
  | grep -v '^#' > "$TMP/test.pp.pnk"
(cd "$ROOT" && lake exe flapjack-compile --assembly "$TMP/test.pp.pnk") \
  > "$TMP/test.S"
test -s "$TMP/test.S"
echo "candidate parse/type check passed ($(wc -l < "$TMP/test.S") assembly lines)"
