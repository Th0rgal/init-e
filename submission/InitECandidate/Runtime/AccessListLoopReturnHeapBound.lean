import InitECandidate.Runtime.AccessListLoopReturnBound
import InitECandidate.Runtime.AccessListLoopHeapBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_access_loop_and_return_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count records input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : AccessHeapLoopWitness state array count records input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeRecords : array.toNat + count.toNat * 16 ≤ records.toNat)
    (countLimit : inputLimit * 32 < 2^64)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (budget : (count.toNat - valid.index.toNat) *
      (accessStepCost inputLength.toNat inputLength.toNat + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessLoopAndReturn
    state.clock ≤ evaluated.2.clock + (count.toNat - valid.index.toNat) *
        (accessStepCost inputLength.toNat inputLength.toNat + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,_,_⟩ := evaluate_access_loop_heap_bounded state
    array count records input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayAbove arrayBeforeRecords countLimit inputBeforeFrame budget
  have bound := evaluate_sequence_straight_bounded state accessLoop
    (.return (.rstruct [.var .local (ofString "recs"),.rfield 1 (.var .local (ofString "lst"))]))
    ((count.toNat - valid.index.toNat) * (accessStepCost inputLength.toNat inputLength.toNat + 1))
    (by rw [run]; exact ⟨cost,remaining,noTimeout⟩) (by decide)
  have terminal := evaluate_seq_terminal state accessLoop
    (.return (.rstruct [.var .local (ofString "recs"),.rfield 1 (.var .local (ofString "lst"))]))
    (fun current => evaluate_return_terminal current _)
  rw [source_access_loop_and_return]
  exact ⟨bound.1,bound.2.1,bound.2.2,terminal⟩

#print axioms evaluate_access_loop_and_return_heap_bounded
end InitECandidate.Runtime
