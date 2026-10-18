import InitECandidate.Runtime.VersionedHashesGuardedRuntimeInvariant
import InitECandidate.Runtime.VersionedHashesUniformSourceStepGuardedHeapBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Each active iteration has a uniform source-clock bound from the actual
heap-cap invariant, including allocation rejection. -/
theorem versioned_hashes_guarded_runtime_invariant_step_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : VersionedHashesGuardedRuntimeInvariant state count array vh input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (countLimit : inputLimit * 120 < 2^64)
    (active : 0 < versionedHashesRank count state)
    (budget : transactionWrapperCallCost inputLength.toNat + (1 + versionedHashesScanCost) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state versionedHashesStep
    state.clock ≤ evaluated.2.clock + (transactionWrapperCallCost inputLength.toNat + (1 + versionedHashesScanCost)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have rank : versionedHashesRank count state = count.toNat - valid.locals.index.toNat := by
    simp [versionedHashesRank,valid.locals.indexLocal]
  have inside : valid.locals.index.toNat < count.toNat := by rw [rank] at active; omega
  obtain ⟨pointer,length,slice⟩ := valid.slices valid.locals.index inside
  exact evaluate_versioned_hashes_uniform_source_step_guarded_heap_bounded state array valid.locals.index input inputLength vh valid.locals.cursor
    valid.locals.arrayLocal valid.locals.indexLocal valid.locals.vhLocal valid.locals.cursorLocal
    pointer length scratch frame valid.heap ceiling inputLimit slice inputBound limitBound
    valid.scratchGlobal valid.frameGlobal valid.locals.code orderedFrame framePositive scratchBelow valid.arena
    valid.heapGlobal valid.heapBound countLimit valid.heapArena inputBeforeFrame valid.inputBeforeHeap
    valid.heapAbove valid.heapAligned budget

#print axioms versioned_hashes_guarded_runtime_invariant_step_bounded
end InitECandidate.Runtime
