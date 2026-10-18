import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- While consumes loop control, and cannot return when its body cannot return. -/
theorem evaluate_while_no_loop_control {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64)
    (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state (.while condition body)).1 ≠ some .break ∧
    (evaluateHOLFiniteState state (.while condition body)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · rename_i word evaluated
    split
    · split
      · simp
      · rename_i nonzero
        dsimp only
        cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
        | mk result post =>
          dsimp only
          have lower : (fixClockHOLFinite (decClockHOLFinite state) (result,post)).2.clock < state.clock := by
            simp only [fixClockHOLFinite,decClockHOLFinite]
            by_cases h : state.clock - 1 < post.clock <;> simp only [h,ite_true,ite_false] <;> omega
          cases result with
          | none => exact evaluate_while_no_loop_control condition body _
          | some result =>
            cases result with
            | «continue» => exact evaluate_while_no_loop_control condition body _
            | «break» => simp
            | returned value => simp
            | error => simp
            | timeOut => simp
            | exception name value => simp
            | finalFfi ffi => simp
    · simp
  · simp
termination_by state.clock
decreasing_by all_goals exact lower

#print axioms evaluate_while_no_loop_control
end InitECandidate.Runtime
