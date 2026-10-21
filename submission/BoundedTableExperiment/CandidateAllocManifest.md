# Candidate allocation execution manifest

## Staging (participant-only, frozen htab fe3f284d2)

- Script: `submission/BoundedTableExperiment/stage_candidate_guest.sh`
- Frozen htab: `submission/BoundedTableExperiment/htab_patricia.pnk`
- Frozen htab sha256: `a97b7463d8f5371a33b92b3f16974f1c8e799bec1c13b71b1c95144b664b7669`
- Generated tree (git-ignored): `submission/CandidateGuestStaging/`
  - `main.pp.pnk` sha256 `aeda9e3b4cc24c6edd53a3bfeda32063f447adb248d4200297825ffe33710376`
  - `CandidateGuestAst.lean` sha256 `4d3530c178b3e1196302a2d65db6433aaff6f3949714a5ac8384384813e602cc`
  - `main.S` sha256 `7ef0543d3a237af22747e0034b6fc9d4ee58c11106bbf75fc05c2621cd9cbd1c`
  - functions: 835
  - `flapjack-compile` exit: 0

## Checked module chain (commit `b9c705e7d`)

| Module | Content | Commit | Axioms |
| --- | --- | --- | --- |
| `ActualCandidateCode.lean` | `candidateRuntimeCode`; `candidate_scratchAllocation_lookup` | `3a5977275` | propext, Classical.choice, Quot.sound |
| `ActualCandidateScratchContract.lean` | lookup-parameterized `scratch_alloc` success decCall contract | `a50053ca0` | same |
| `ActualCandidateCodeNames.lean` | body-free names; absence reduction | `6b95640af` | same |
| `ActualCandidateProgConversion.lean` | program head conversion lemmas | `b3de8e9b0` | same |
| `ActualCandidateKeysHead.lean` | header through `keys <- alloc (cap*stride)`, opaque tail | `d537f94d5` | same |
| `ActualCandidateScratchEval.lean` | lookup-only scratch call evaluation; `candidate_htabNewScratch_first_alloc_eval` (actual 120-byte `t` allocation) | `b9c705e7d` | same |

No `sorryAx`. The checked semantic claim is the **first** allocation only. The
header continuation (stride, four stores) before the `keys` call is not yet
executed, so the allocation bases and `path = nodesEnd` remain open.
