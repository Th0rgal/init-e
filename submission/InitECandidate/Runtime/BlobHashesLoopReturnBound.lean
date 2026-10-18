import InitECandidate.Runtime.BlobHashesLoopBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_blobHashes_loop_and_return_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array count buffer input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : BlobHashesLoopWitness state array count buffer input inputLength scratch frame ceiling)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arrayBeforeFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (arrayBeforeBuffer : array.toNat + count.toNat * 16 ≤ buffer.toNat)
    (aligned : buffer.toNat % 8 = 0) (fits : buffer.toNat + count.toNat * 32 ≤ 2^64)
    (budget : (count.toNat - valid.index.toNat) *
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state blobHashesLoopAndReturn
    state.clock ≤ evaluated.2.clock + (count.toNat - valid.index.toNat) *
        (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,_,_⟩ := evaluate_blobHashes_loop_bounded state
    array count buffer input inputLength scratch frame ceiling inputLimit valid inputBound limitBound orderedFrame framePositive
    scratchBelow arrayBeforeFrame arrayBeforeBuffer aligned fits budget
  have bound := evaluate_sequence_straight_bounded state blobHashesLoop
    (.return (.rstruct [.var .local (ofString "buf"),.rfield 1 (.var .local (ofString "lst"))]))
    ((count.toNat - valid.index.toNat) * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651))
    (by rw [run]; exact ⟨cost,remaining,noTimeout⟩) (by decide)
  have terminal := evaluate_seq_terminal state blobHashesLoop
    (.return (.rstruct [.var .local (ofString "buf"),.rfield 1 (.var .local (ofString "lst"))]))
    (fun current => evaluate_return_terminal current _)
  rw [source_blobHashes_loop_and_return]
  exact ⟨bound.1,bound.2.1,bound.2.2,terminal⟩

#print axioms evaluate_blobHashes_loop_and_return_bounded
end InitECandidate.Runtime
