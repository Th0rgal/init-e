import InitECandidate.Runtime.RlpValidationLoopInvariant
import InitECandidate.Runtime.RlpValidationParseNamedGlobal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every normally completed validator step retains frame_mem_ptr, including
the final iteration that clears go and therefore needs no successor witness. -/
theorem rlpValidation_normal_step_named_global {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (watched : MlS) (different : ofString "scratch_ptr" ≠ watched)
    (frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : RlpValidationLoopWitness state frame ceiling inputLimit) (ticks : 14 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpValidationStep = (none,post)) :
    post.globals.lookup watched = state.globals.lookup watched := by
  by_cases finished : valid.position = valid.stop
  · have atPosition : state.locals.lookup (ofString "pos") = some (.val (.word valid.stop)) := by
      simpa [finished] using valid.positionLocal
    cases framesEq : valid.frames with
    | nil =>
      have atTop : state.locals.lookup (ofString "top") = some (.val (.word 0)) := by
        simpa [framesEq,rlpValidationStackTop] using valid.topLocal
      have actual := evaluate_rlpValidation_finish_empty state valid.stop valid.flag atPosition valid.stopLocal atTop valid.flagLocal
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      rw [same]
      rfl
    | cons saved rest =>
      have atTop : state.locals.lookup (ofString "top") = some (.val (.word saved.record)) := by
        simpa [framesEq,rlpValidationStackTop] using valid.topLocal
      have stack : RlpValidationStack state.memory valid.scratch.toNat (saved :: rest) := by
        simpa [framesEq] using valid.stack
      have readable := valid.stack.readable state valid.stackCeiling (by
        intro address lower upper
        apply valid.arena address _ upper
        have ordered := BitVec.le_def.mp valid.orderedFrame
        omega)
      have domains := readable saved (by rw [framesEq]; simp)
      obtain ⟨output,popRun,_,globals⟩ := evaluate_rlpValidation_stack_pop_scope state valid.stop valid.stop valid.scratch.toNat saved rest
        atPosition valid.stopLocal atTop stack domains.1 domains.2.1 domains.2.2
      have actual := (evaluate_rlpValidation_step_stack_pop state valid.stop valid.scratch.toNat saved rest
        atPosition valid.stopLocal atTop stack).trans popRun
      have same := (Prod.mk.inj (run.symm.trans actual)).2
      rw [same,globals]
  · have headerRun := (evaluate_rlpValidation_step_header state valid.position valid.stop
      valid.positionLocal valid.stopLocal finished).symm.trans run
    exact rlpValidation_parse_named_global state post watched different valid.position valid.stop valid.scratch frame valid.frames
      valid.positionLocal valid.stopLocal valid.topLocal valid.scratchGlobal valid.frameGlobal valid.code ticks valid.orderedFrame
      (by intro address lower upper; exact valid.arena address lower (by have below := valid.scratchBelow; omega)) headerRun

#print axioms rlpValidation_normal_step_named_global
end InitECandidate.Runtime
