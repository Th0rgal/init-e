import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- An actual returned declaration-call cannot start with zero clock,
regardless of argument or function-lookup failures. -/
theorem evaluate_decCall_returned_nonzero_clock {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) =
      (some (.returned value),post)) : state.clock ≠ 0 := by
  intro zero
  rw [evaluateHOLFiniteState_decCall_total] at run
  cases args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => rw [args] at run; simp at run
  | some values =>
    rw [args] at run
    dsimp only at run
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [lookup] at run; simp at run
    | some found =>
      obtain ⟨body,locals,returnShape⟩ := found
      rw [lookup] at run
      simp [zero] at run

#print axioms evaluate_decCall_returned_nonzero_clock
end InitECandidate.Runtime
