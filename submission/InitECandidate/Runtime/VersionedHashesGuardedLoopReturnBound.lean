import InitECandidate.Runtime.VersionedHashesLoopReturnBound
import InitECandidate.Runtime.VersionedHashesGuardedRuntimeLoopBound
import InitECandidate.Runtime.PanSeqStraightBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_versioned_hashes_guarded_loop_return_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (count array vh input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : VersionedHashesGuardedRuntimeInvariant state count array vh input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (countLimit : inputLimit * 120 < 2^64)
    (budget : versionedHashesRank count state * (versionedHashesTransactionStepCost inputLength.toNat + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (versionedHashesAt 7)
    state.clock ≤ evaluated.2.clock + versionedHashesRank count state * (versionedHashesTransactionStepCost inputLength.toNat + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  obtain ⟨result,post,run,spent,remaining,noTimeout,_⟩ := evaluate_versioned_hashes_guarded_runtime_loop_bounded state
    count array vh input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive scratchBelow inputBeforeFrame arrayAbove countLimit budget
  have bounded : state.clock ≤ (evaluateHOLFiniteState state versionedHashesLoop).2.clock +
      versionedHashesRank count state * (versionedHashesTransactionStepCost inputLength.toNat + 1) ∧
      (evaluateHOLFiniteState state versionedHashesLoop).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state versionedHashesLoop).1 ≠ some .timeOut := by
    rw [run]; exact ⟨spent,remaining,noTimeout⟩
  rw [source_versioned_hashes_loop_return]
  exact evaluate_sequence_straight_bounded state versionedHashesLoop versionedHashesReturnTail _ bounded (by rfl)

#print axioms source_versioned_hashes_loop_return
#print axioms evaluate_versioned_hashes_guarded_loop_return_bounded
end InitECandidate.Runtime
