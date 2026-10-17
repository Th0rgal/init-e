import InitECandidate.Runtime.RlpValidationLoopInvariant
import InitECandidate.Runtime.RlpValidationHeaderBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual validator step from its invariant has a fourteen-tick bound,
including terminal parsing/allocator failures; completed intervals cost no ticks. -/
theorem evaluate_rlpValidation_step_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : RlpValidationLoopWitness state frame ceiling inputLimit) (ticks : 14 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpValidationStep
    state.clock ≤ evaluated.2.clock + 14 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases finished : valid.position = valid.stop
  · have atPosition : state.locals.lookup (ofString "pos") = some (.val (.word valid.stop)) := by
      simpa [finished] using valid.positionLocal
    cases framesEq : valid.frames with
    | nil =>
      have atTop : state.locals.lookup (ofString "top") = some (.val (.word 0)) := by
        simpa [framesEq,rlpValidationStackTop] using valid.topLocal
      rw [evaluate_rlpValidation_finish_empty state valid.stop valid.flag atPosition valid.stopLocal atTop valid.flagLocal]
      exact ⟨by change state.clock ≤ state.clock + 14; omega,Nat.le_refl _,by simp⟩
    | cons saved rest =>
      have atTop : state.locals.lookup (ofString "top") = some (.val (.word saved.record)) := by
        simpa [framesEq,rlpValidationStackTop] using valid.topLocal
      have stack : RlpValidationStack state.memory valid.scratch.toNat (saved :: rest) := by
        simpa [framesEq] using valid.stack
      have intervals : RlpValidationIntervals valid.stop valid.stop (saved :: rest) := by
        simpa [finished,framesEq] using valid.intervals
      have readable := valid.stack.readable state valid.stackCeiling (by
        intro address lower upper
        apply valid.arena address _ upper
        have ordered := BitVec.le_def.mp valid.orderedFrame
        omega)
      have domains := readable saved (by rw [framesEq]; simp)
      obtain ⟨post,run,_,_,_,_,_,_,clock,_⟩ := evaluate_rlpValidation_pop_invariant state valid.stop valid.scratch.toNat saved rest
        atPosition valid.stopLocal atTop stack intervals domains.1 domains.2.1 domains.2.2
      rw [run]
      dsimp only
      exact ⟨by omega,by omega,by simp⟩
  · rw [evaluate_rlpValidation_step_header state valid.position valid.stop valid.positionLocal valid.stopLocal finished]
    exact evaluate_rlpValidation_header_bounded state valid.position valid.stop valid.scratch frame
      valid.positionLocal valid.stopLocal valid.scratchGlobal valid.frameGlobal valid.code ticks

#print axioms evaluate_rlpValidation_step_bounded
end InitECandidate.Runtime
