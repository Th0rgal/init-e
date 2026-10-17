import InitECandidate.Runtime.RlpListCountLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful enabled counting loop exposes its actual first iteration
and the remaining loop at the evaluator's clock-corrected state. -/
theorem rlpListCount_loop_normal_tail {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (offset length : BitVec 64)
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (enabled : offset.toNat < length.toNat)
    (run : evaluateHOLFiniteState state rlpListCountLoop = (none,post)) :
    ∃ middle : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState (decClockHOLFinite state) rlpListCountStep = (none,middle) ∧
      evaluateHOLFiniteState (fixClockHOLFinite (decClockHOLFinite state) ((none : Option (PanSemResultExact 64)),middle)).2 rlpListCountLoop = (none,post) := by
  have guard : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .lower (.var .local (ofString "off")) (.var .local (ofString "len"))) = some (.val (.word 1)) := by
    simp [evalHOLFinite,evalHOLExact,offsetLocal,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled]
  rw [source_rlpListCount_loop,evaluateHOLFiniteState_while_total,guard] at run
  dsimp only at run
  by_cases zero : state.clock = 0
  · simp [zero] at run
  · rw [if_neg zero] at run
    have control := evaluate_rlpListCount_step_control (decClockHOLFinite state)
    cases step : evaluateHOLFiniteState (decClockHOLFinite state) rlpListCountStep with
    | mk result middle =>
      rw [step] at run control
      dsimp only at control
      cases result with
      | none =>
        refine ⟨middle,rfl,?_⟩
        rw [source_rlpListCount_loop]
        exact run
      | some stopped =>
        cases stopped <;> simp_all [fixClockHOLFinite]

#print axioms rlpListCount_loop_normal_tail
end InitECandidate.Runtime
