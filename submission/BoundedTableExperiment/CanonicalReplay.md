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
10. `ActualFindLeafStepFrame.lean` (guard/push/bump node frames, guard internal tag)
11. `ActualFindLeafRouteChild.lean` (route/byte/mask/child node restore)
12. `ActualTaggedTrie.lean` (tagged internal live-edge invariant, root leaf/empty/internal)
13. `ActualPushTrieFrame.lean` (actual push slot vs node cells)
14. `ActualWordSepFrame.lean` (canonical WordSep node-cell frame, no-wrap disjointness)
15. `ActualSlabPathFrame.lean` (slab cells below path)
16. `ActualCandidateHeap.lean` (candidate heap invariant and push preservation)
17. `ActualCandidateAllocSeq.lean` (frozen candidate allocation call order and arguments)
18. `ActualCandidateScratchContract.lean` (lookup-parameterized scratch_alloc success contract)
19. `ActualCandidateCodePrefix.lean` (generic lookup prefix skip)
20. `ActualCandidateCodeNames.lean` (body-free names; absence reduction)
21. `ActualCandidateCode.lean` (candidateRuntimeCode and scratch_alloc lookup)

Latest checked commits: `08ee26dd5`, `4513efed8`, `69fd41bfe`, `12a59902b`,
`254cf589b`, `3f4990b6c`, `6be500f0d`, `5560cba5c`, `97bdde03e`,
`41be50a52`, `5e4fb84e0`, `33fe26cf9`, `13ef3caa5`, `9a0ec6c9f`,
`a75b79af4`, `a50053ca0`, `ebeedaea8`, `b3aab0765`, `6b95640af`,
`3a5977275`.

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
- Preserve the tagged `CandidateHeapInv` through `htab_set`, `grow`, and `del`.
- Allocator tie is open: `InitECandidate.Runtime.HtabRegions` describes the
  original runtime `htab_new_scratch` (72-byte header, no nodes/path), not the
  frozen candidate (120-byte header, nodes at offset 96, path at 104, no `used`).
  A candidate-specific `source_htabNewScratch_body` and scratch sequence region
  theorem are required before claiming `path = nodesEnd` or live slab ownership.
