import InitECandidate.Runtime.VersionedHashesGuardedRuntimeInvariant
import InitECandidate.Runtime.VersionedHashesUniformSourceStepGuardedHeapGrowth
import InitECandidate.Runtime.VersionedHashesSourceStepGuardedHeapOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem versioned_hashes_guarded_runtime_invariant_step {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : VersionedHashesGuardedRuntimeInvariant state count array vh input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (arrayAbove : ceiling ≤ array.toNat)
    (countLimit : inputLimit * 120 < 2^64)
    (active : 0 < versionedHashesRank count state)
    (budget : transactionWrapperCallCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    Nonempty (VersionedHashesGuardedRuntimeInvariant post count array vh input inputLength scratch frame ceiling) ∧
      versionedHashesRank count post < versionedHashesRank count state := by
  have rank : versionedHashesRank count state = count.toNat - valid.locals.index.toNat := by
    simp [versionedHashesRank,valid.locals.indexLocal]
  have inside : valid.locals.index.toNat < count.toNat := by rw [rank] at active; omega
  obtain ⟨pointer,length,slice⟩ := valid.slices valid.locals.index inside
  have lengthBound := slice.length_bound state array valid.locals.index pointer length input inputLength
  obtain ⟨nextHeap,binding,lower,upper,heapBound,aligned,scratchFinal,frameFinal⟩ := versioned_hashes_uniform_source_step_guarded_heap_growth state post
    array valid.locals.index input inputLength vh valid.locals.cursor valid.locals.arrayLocal valid.locals.indexLocal valid.locals.vhLocal
    valid.locals.cursorLocal pointer length scratch frame valid.heap ceiling inputLimit slice inputBound limitBound valid.scratchGlobal valid.frameGlobal
    valid.locals.code orderedFrame framePositive scratchBelow valid.arena valid.heapGlobal valid.heapBound countLimit valid.heapArena
    inputBeforeFrame valid.inputBeforeHeap valid.heapAligned budget array count input inputLength valid.slices arrayAbove valid.arrayBeforeHeap run
  have cost := transaction_wrapper_call_cost_mono length.toNat inputLength.toNat lengthBound
  have slices := versioned_hashes_source_step_normal_guarded_heap_outer_prefix state post array valid.locals.index input inputLength vh valid.locals.cursor
    valid.locals.arrayLocal valid.locals.indexLocal valid.locals.vhLocal valid.locals.cursorLocal pointer length scratch frame valid.heap ceiling inputLimit
    slice inputBound limitBound valid.scratchGlobal valid.frameGlobal valid.locals.code orderedFrame framePositive scratchBelow valid.arena
    valid.heapGlobal valid.heapBound countLimit valid.heapArena inputBeforeFrame valid.inputBeforeHeap valid.heapAligned (cost.trans budget)
    array count input inputLength valid.slices arrayAbove valid.arrayBeforeHeap run
  obtain ⟨⟨locals⟩,decreases⟩ := versioned_hashes_locals_invariant_step state post count array vh valid.locals active run
  have metadata := evaluateHOLFiniteState_metadata state versionedHashesStep
  rw [run] at metadata
  refine ⟨⟨⟨locals,slices,nextHeap,binding,scratchFinal,frameFinal,aligned,heapBound,?_,?_,
    valid.inputBeforeHeap.trans lower,valid.arrayBeforeHeap.trans lower,valid.heapAbove.trans lower⟩⟩,decreases⟩
  · intro address low high; rw [metadata.2.1]; exact valid.arena address low high
  · intro address low high; rw [metadata.2.1]; exact valid.heapArena address (lower.trans low) high

#print axioms versioned_hashes_guarded_runtime_invariant_step
end InitECandidate.Runtime
