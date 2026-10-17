import InitECandidate.Runtime.RlpSlicesLoopBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful enabled filling loop exposes its actual first iteration
and the remaining loop at the evaluator's clock-corrected state. -/
theorem rlpSlices_loop_normal_tail {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64)
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (enabled : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state rlpSlicesLoop = (none,post)) :
    ∃ middle : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState (decClockHOLFinite state) rlpSlicesStep = (none,middle) ∧
      evaluateHOLFiniteState (fixClockHOLFinite (decClockHOLFinite state) ((none : Option (PanSemResultExact 64)),middle)).2 rlpSlicesLoop = (none,post) := by
  have guard : evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))) = some (.val (.word 1)) := by
    simp [evalHOLFinite,evalHOLExact,indexLocal,countLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,enabled]
  rw [source_rlpSlices_loop,evaluateHOLFiniteState_while_total,guard] at run
  dsimp only at run
  by_cases zero : state.clock = 0
  · simp [zero] at run
  · rw [if_neg zero] at run
    have control := evaluate_rlpSlices_step_control (decClockHOLFinite state)
    cases step : evaluateHOLFiniteState (decClockHOLFinite state) rlpSlicesStep with
    | mk result middle =>
      rw [step] at run control
      dsimp only at control
      cases result with
      | none =>
        refine ⟨middle,rfl,?_⟩
        rw [source_rlpSlices_loop]
        exact run
      | some stopped =>
        cases stopped <;> simp_all [fixClockHOLFinite]

#print axioms rlpSlices_loop_normal_tail
end InitECandidate.Runtime
