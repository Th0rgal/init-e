# finite-vm handoff (STOPPED)

Branch: feat/bounded-table-experiment
Checkout: /home/zksecurity/trim-space/init-e/work/cost-guest-checkout
Last verified clean HEAD: 2ae8abba3 (pushed)
Tree: only work/ additions in the handoff commit; no challenge files touched.

## Stop reason
finite-lead relayed USER STOP: challenge being reworked. Stopped at atomic boundary; no
further builds/tasks started; no auto-continue watcher owned.

## Full-guest staging (participant-only, unchanged)
- Script: submission/BoundedTableExperiment/stage_candidate_guest.sh
- Frozen replacement htab: submission/BoundedTableExperiment/htab_patricia.pnk
  sha256 a97b7463d8f5371a33b92b3f16974f1c8e799bec1c13b71b1c95144b664b7669 (commit fe3f284d2)
- Generated (git-ignored) under submission/CandidateGuestStaging/:
  main.pp.pnk aeda9e3b4cc24c6edd53a3bfeda32063f447adb248d4200297825ffe33710376
  CandidateGuestAst.lean 4d3530c178b3e1196302a2d65db6433aaff6f3949714a5ac8384384813e602cc
  main.S 7ef0543d3a237af22747e0034b6fc9d4ee58c11106bbf75fc05c2621cd9cbd1c
  835 functions; flapjack-compile exit 0

## Checked results (all print axioms subset of propext, Classical.choice, Quot.sound; no sorryAx)
HEAD 2ae8abba3  ActualCandidateAllocHeapFrame.lean
- candidate_alloc_skip_heap: completed scratch_alloc preserves memory; sets scratch_ptr = scratchAllocationEnd pointer size.
- candidate_alloc_skip_heap_pointer: same run names scratch_ptr = aligned allocation end.

HEAD fc515f5af  ActualCandidateLoopRank.lean
- body_counterRank_step: every continuing run of frozen body
  `st vals + i*8, i+2; i = i+1` increments counterRank by one.
- guard_value_word / guard_lower_word(_bit): word-valued and nonzero `i<cap` guard semantics.
- whileCount_counter_le_cap_strict: counterRank s + n <= cap (exact frozen loops
  htab_patricia.pnk lines 51-54 and 89-92), no 480 assumption.
- candidate_capacity_init_cost_linear: n <= cap and
  work <= cap*(head+nativeCost*98+bodyStore+bodyAssign)
          +(statement+head+nativeCost*98).
  NOTE: this is the frozen table-capacity init loop, NOT route depth.

Prior checked chain (all pushed):
- ActualStoreWorkDecomposition: executionWork_store_events / _assign_events.
- ActualCandidateLoopBodyPrice: body prices 132/61/61, wordness, flatten length 1.
- ActualCandidateLoopBodyBound: store/assign/body run bounds; candidate_loop_body_bounded_cost(_of_words).
- ActualWhileBoundedStep: whileCount_le_480_none (continuing-only rank), bitvec_succ_toNat.
- ActualWhileHeadCost / ActualWhileUniformCost / ActualWhileRouteBound / ActualWhileIterationWork.

## WIP preserved (UNVERIFIED, not imported anywhere)
work/wip_ActualCandidateAllocChain.lean
- Goal: candidate_alloc_skip_locals: a completed scratch_alloc decCall (.skip tail) leaves
  every other local unchanged (cap survives each of the six frozen allocation frames).
- Status: builds partially; final goal after framing is
  (state.locals.update (name, word (scratchAllocationEnd pointer size))).lookup name' =
   state.locals.lookup name'
  with hne : name' ≠ name. Last error: rewrite/update-lookup orientation; simp with
  HolFiniteMapExact.lookup_update + hne should close it.
- It is NOT part of the build and is not committed as a module.

## Remaining issues / restart instructions
1. Finish locals-preservation lemma, then chain the six allocation frames
   (vals/order/order_pos/nodes/path), deriving actual bases and path = nodesEnd from runs.
2. Compose capacity init cost with allocation frames into htab_new_scratch cost.
3. Relate capacity/growth to live entries and gas (separate step).
4. Route-depth 480 invariant belongs to tagged-node traversal guard (internal-node pointer),
   not capacity loops.
5. Source event migration: finite-auth owns source pricing; awaiting exact migration commit SHA
   + event replay manifest. Expression prices unchanged by raise-only retune.
Build env:
  SHARED=$(cat /home/zksecurity/trim-space/init-e/work/finite-auth-work/shared_lean_path.txt)
  export LEAN_PATH="submission/CandidateGuestStaging:.build:price-harness/.build:$SHARED:/home/zksecurity/trim-space/init-e/work/cost-source-build/lib/lean"
  LEAN=/home/zksecurity/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean
Rebuild dependency oleans with `-o .build/<Name>.olean` when a module changes.
