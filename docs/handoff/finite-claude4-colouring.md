# Handoff: finite-claude4, register colouring/allocation executed-cost transfer

Stopped on request (user reworking the challenge), 2026-10-21 ~16:15 UTC.

- Branch: `feat/claude4-colouring-cost`, checkout `/home/claude4/work/init-e` (user `claude4`).
- Base: `e2e6734b9`. The branch was never pushed (no GitHub credentials for `claude4`).
- Bundle (refreshed at stop): `/var/tmp/claude4-share/colouring-latest.bundle`, range `e2e6734b9..feat/claude4-colouring-cost`.
  Fetch with `git fetch /var/tmp/claude4-share/colouring-latest.bundle feat/claude4-colouring-cost`.

## Commits (oldest first)

| SHA | Content | Status |
|---|---|---|
| `32c23e9d0` | Uniform local colouring + wordAlloc/wordAllocWith cost | CHECKED |
| `f9f354dcd` | cherry-pick of root `3ce7d38f5` (WordArityCodeMap, FullSSACodeTable, ...) | root's |
| `394b63720` | cherry-pick of root `c93ef0ce9` (function-indexed counter) | root's |
| `3a4938d62` | cherry-pick of root `e7f7e1bae` (indexed permutation) + WordPermuteGlobalCost import fix (same as root `f3914600c`) | root's + fix |
| `d4d324cbd` | Indexed colouring: basis/control/loop | CHECKED |
| `192e891b7` | Indexed colouring: tail + returning calls | CHECKED |
| `20331af18` | Indexed colouring: global/whole-table theorem | CHECKED |
| (this commit) | WIP `WordAllocationClockCost.lean.wip` + this handoff | UNVERIFIED (WIP) |

"CHECKED" means a private build of the module with `tools/limited-lake.py --slots 4` (exit 0, no `sorryAx`). Every exported theorem uses only `[propext, Classical.choice, Quot.sound]` or a subset. No `sorry`, `admit`, `native_decide`, `bv_decide` or custom axioms appear in the checked modules.
Log of the last full check: `/var/tmp/claude4-share/colour-indexed-build.log` (targets `WordColourIndexedGlobal` and `WordColourAlloc`).

## Checked results (`submission/InitECandidate/Runtime/`)

**Uniform, same code table**

- `WordColourPrice`:
  - `wordOptimizerLocalPrice (applyColour f p) s = wordOptimizerLocalPrice p s` for every `f`, spilling colourings included.
  - `wordCostSupported_applyColour`.
- `WordColourCostBasis`, `WordColourCostLoop`, `WordColourCostCall`, `WordColourCostReturn`:
  - The quantitative `evaluate_apply_colour` (`ColourCostPost`/`ColourCostGoal`).
- `WordColourAlloc`:
  - `colourCostGoal_all`.
  - `wordAlloc_cost` covers all branches (oracle, select, fallback).
  - `wordAllocWith_cost` for `ra = regAlloc`.
  - `wordAllocWith_oracle_cost` for any `ra` with an accepted oracle.
  - `wordOptimizerPrice_colourInvariant`.
  - Contract `AllocCostPost`: the `word_alloc_correct` conclusion plus `cost(allocated, st) <= cost(prog, st{perm})`.

**Function-indexed, mapped tables (supersedes the uniform split for tighter prices)**

- `WordColourIndexed{Basis,Control,Loop,Tail,Return,Global}`.
- Main theorem `colourIndexed_table`:
  - **Premises:**
    - `ColourAllocTable source target col`: target entry = `applyColour (col label) body`.
    - `ColourTableFacts`: per label, `colouringOk`, physical registers fixed, and no install.
    - `noInstallCode` for both tables.
    - Leaf bound `TP (applyColour (col l) p) <= SP l p`.
    - A source entry state with even locals.
  - **Conclusion:** `ColourIndexedPost`. One source scheduler gives the same result, `wordStateEqRel` modulo code, HOL live-scoped locals, and
    `wordExecutionCost TP (target body) <= wordFunctionExecutionCost SP label (source body)`.
  - The permutation premise is discharged by root's `word_function_permute_executed_cost`.
- `colourIndexed_table_ghost` instantiates the ghost price `SP l p := TP (applyColour (col l) p)`.
- `colourTableEntry_of_oracle` gives the per-entry facts from the production `oracleColourOk`.

## Measurements (not proofs)

`/var/tmp/claude4-share/ColourWalk.lean` and its output `ColourWalk.out.txt` cover the ADD path using finite-auth's walker. The walker reproduces isel 10182, SSA 15678, removeDead 13182 and final 10206 at optP.

| Price on the same ADD path | Total |
|---|---|
| SSA priced by the final colouring `f` (exact `12 * parmove`) | 9858 |
| removeDead, same price | 8310 |
| pre-alloc, same price | 5358 |
| final allocated, exact refined price | 5358 |

Frame audit: 752 frames in the `Proofs/BackendStages` chunk literals; maximum 67 (limit 92). The candidate835-vs-canonical comparison was not done.

## Unverified / remaining

1. **`WordAllocationClockCost.lean.wip`** (renamed so that no build picks it up). It proves that executed cost is unchanged by extra clock on runs that don't time out (companion of `evaluate_add_clock`), which `removeMustTerminate` cost needs. Status at stop: one error left, "`simp` made no progress" around line 340 in `clock_cost_returning`, exception branch.
   - **To restart:** rename it back to `.lean`, run `lake env lean` on it, and fix that branch (likely `simp only [mismatch, if_true]` → `simp [mismatch]`).
   - The `removeMustTerminate` transfer itself is not started; it should mirror `word_remove_correct_aux` with costs.
2. Building `ColourAllocTable` for the ACTUAL compiled word table from the per-function `wordAllocWith` outputs: labels and oracle indices zip in compile order. This needs root's table-construction facts.
3. Upstream: the SSA → post-SSA chain must carry the indexed ghost source price `Q_f` (root/finite-auth). Root reported possible strict per-site funding failures even where totals fit.
4. The superseded uniform-table draft is kept only in the scratchpad (not committed).

## Restart instructions

- Toolchain `~/.elan` (Lean v4.33.1), private `.lake` in this checkout.
- Build helper: `python3 tools/limited-lake.py --work-dir $PWD/.lake/lean-limit --slots 4 -- lake build <Module>`.
- Messaging: agmsg team `init-e-finite`, identity `finite-claude4`. Scripts must run via `sg users -c` because `claude4` was added to group `users` mid-session. Delivery was set to `off` at stop.
