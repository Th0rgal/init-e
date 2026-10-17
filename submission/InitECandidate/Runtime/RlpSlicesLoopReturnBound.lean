import InitECandidate.Runtime.RlpSlicesLoopBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpSlices_loop_and_return : rlpSlicesLoopAndReturn =
    .seq rlpSlicesLoop (.return (.rstruct [.var .local (ofString "arr"),.var .local (ofString "count")])) := by
  simp only [rlpSlicesLoopAndReturn,rlpSlicesLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original final return adds no ticks and cannot fall through,
including failed return-value checks after a normal slice loop. -/
theorem evaluate_rlpSlices_loop_and_return_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64) (valid : RlpSlicesLoopWitness state pointer count)
    (budget : (count.toNat - valid.index.toNat) * 12 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpSlicesLoopAndReturn
    state.clock ≤ evaluated.2.clock + (count.toNat - valid.index.toNat) * 12 ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  obtain ⟨result,post,run,cost,remaining,noTimeout,_,_⟩ := evaluate_rlpSlices_loop_bounded state pointer count valid budget
  have bound := evaluate_sequence_straight_bounded state rlpSlicesLoop
    (.return (.rstruct [.var .local (ofString "arr"),.var .local (ofString "count")]))
    ((count.toNat - valid.index.toNat) * 12) (by rw [run]; exact ⟨cost,remaining,noTimeout⟩) (by decide)
  have terminal := evaluate_seq_terminal state rlpSlicesLoop
    (.return (.rstruct [.var .local (ofString "arr"),.var .local (ofString "count")]))
    (fun current => evaluate_return_terminal current _)
  rw [source_rlpSlices_loop_and_return]
  exact ⟨bound.1,bound.2.1,bound.2.2,terminal⟩

#print axioms evaluate_rlpSlices_loop_and_return_bounded
end InitECandidate.Runtime
