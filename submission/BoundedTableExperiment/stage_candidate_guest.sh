#!/usr/bin/env bash
# Participant-only full-guest staging: canonical guest sources with the frozen
# Patricia htab replacement. Never writes under challenge Guest/ or guest/.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
STAGE="$ROOT/submission/CandidateGuestStaging"
FROZEN="$ROOT/submission/BoundedTableExperiment/htab_patricia.pnk"

rm -rf "$STAGE"
mkdir -p "$STAGE"
cp -R "$ROOT/guest/src/." "$STAGE/src/"
cp "$FROZEN" "$STAGE/src/lib/htab.pnk"

cpp -P -w -nostdinc -I "$STAGE/src" -x c "$STAGE/src/main.pnk" \
  | grep -v '^#' > "$STAGE/main.pp.pnk"

(cd "$ROOT" && lake exe gen-guest-ast "$STAGE/main.pp.pnk" CandidateGuest) \
  > "$STAGE/CandidateGuestAst.lean"

(cd "$ROOT" && lake exe flapjack-compile --assembly "$STAGE/main.pp.pnk") \
  > "$STAGE/main.S"

test -s "$STAGE/CandidateGuestAst.lean"
test -s "$STAGE/main.S"
echo "staging: $STAGE"
sha256sum "$FROZEN" "$STAGE/src/lib/htab.pnk" "$STAGE/main.pp.pnk" \
  "$STAGE/CandidateGuestAst.lean" "$STAGE/main.S"
echo "functions: $(grep -c 'Decl.function' "$STAGE/CandidateGuestAst.lean")"
echo "assembly lines: $(wc -l < "$STAGE/main.S")"
