import InitECandidate.Runtime.KeccakAlignedOutput
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The exact original hash suffix after the short-input copy is bounded by
nineteen ticks for aligned output, including every early memory or external exit. -/
theorem evaluate_keccak_padded_tail_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad output : BitVec 64)
    (stp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (aligned : output.toNat % 8 = 0)
    (code : state.code = originalRuntimeCode) (ticks : 19 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keccakAfterCopy = (result,post) ∧
      state.clock ≤ post.clock + 19 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  obtain ⟨result,middle,run,cost,remaining,noTimeout,locals,_,_,_⟩ := evaluate_keccak_padding_absorb_bounded state pointer pad stp padGlobal code ticks
  rw [evaluate_keccak_padding_absorb_group,evaluateHOLFiniteState_seq_line780,run]
  cases result with
  | none =>
    have atOut : middle.locals.lookup (ofString "out") = some (.val (.word output)) := by
      rw [locals rfl]
      exact outLocal
    have tail := evaluate_keccak_aligned_output middle output atOut aligned
    cases outputRun : evaluateHOLFiniteState middle keccakOutputScope with
    | mk finalResult post =>
      rw [outputRun] at tail
      dsimp only at tail
      exact ⟨finalResult,post,outputRun,by omega,by omega,tail.2⟩
  | some result => exact ⟨some result,middle,rfl,cost,remaining,noTimeout⟩

#print axioms evaluate_keccak_padded_tail_bounded
end InitECandidate.Runtime
