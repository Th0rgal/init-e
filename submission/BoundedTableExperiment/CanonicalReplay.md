# BoundedTableExperiment canonical replay

Frozen candidate source: `submission/BoundedTableExperiment/htab_patricia.pnk`
sha256 `a97b7463d8f5371a33b92b3f16974f1c8e799bec1c13b71b1c95144b664b7669`
(frozen commit `fe3f284d2`).

## Full guest staging (participant-only)

Script: `submission/BoundedTableExperiment/stage_candidate_guest.sh`

Generated tree: `submission/CandidateGuestStaging/` (git-ignored)

- `main.pp.pnk` sha256 `aeda9e3b4cc24c6edd53a3bfeda32063f447adb248d4200297825ffe33710376`
- `CandidateGuestAst.lean` sha256 `4d3530c178b3e1196302a2d65db6433aaff6f3949714a5ac8384384813e602cc`
- `main.S` sha256 `7ef0543d3a237af22747e0034b6fc9d4ee58c11106bbf75fc05c2621cd9cbd1c`
- functions: 835; `flapjack-compile` exit 0

## Checked Lean chain

1. `ActualPathMemoryInvariant.lean`
2. `ActualLinkMemoryInvariant.lean`
3. `ActualRouteDepthBound.lean`
4. `CandidateFindLeafShape.lean`
5. `ActualLoadBridge.lean`
6. `ActualLiveTrieInvariant.lean`
7. `ActualWhileCount.lean`
8. `ActualWhileRouteBound.lean`
9. `ActualRouteSequenceBound.lean`

Latest checked commits: `08ee26dd5`, `4513efed8`, `69fd41bfe`.

## Replay

```sh
cd /home/zksecurity/trim-space/init-e/work/cost-guest-checkout
SHARED=$(cat /home/zksecurity/trim-space/init-e/work/finite-auth-work/shared_lean_path.txt)
export LEAN_PATH=".build:price-harness/.build:$SHARED:/home/zksecurity/trim-space/init-e/work/cost-source-build/lib/lean"
lean -o .build/ActualRouteDepthBound.olean submission/BoundedTableExperiment/ActualRouteDepthBound.lean
lean -o .build/ActualLoadBridge.olean submission/BoundedTableExperiment/ActualLoadBridge.lean
lean submission/BoundedTableExperiment/ActualLiveTrieInvariant.lean
lean submission/BoundedTableExperiment/ActualWhileRouteBound.lean
lean submission/BoundedTableExperiment/ActualRouteSequenceBound.lean
```

All checked theorems use only `propext`, `Classical.choice`, `Quot.sound`.

## Open obligations

- Instantiate `whileCount_le_480` rank with the decoded node route from the full
  `candidateFindLeafStep` body run, including guard-skip, push, bump, route,
  byte/mask, and child selection; handle the initial leaf case without a route
  load.
- Preserve `TrieInv` through `htab_set`, `grow`, and `del`.
