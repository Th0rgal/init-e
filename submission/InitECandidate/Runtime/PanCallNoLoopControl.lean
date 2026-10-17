import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- An unhandled discard call converts callee break/continue to error;
these controls cannot escape into the caller's loop. -/
theorem evaluate_discard_call_no_loop_control {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 ≠ some .break ∧
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call]
  cases argsRun : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => simp
  | some values =>
    simp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => simp
    | some data =>
      obtain ⟨body,callee,returnShape⟩ := data
      simp only
      by_cases zero : state.clock = 0
      · simp [zero]
      · simp only [if_neg zero]
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
        | mk result post =>
          cases result with
          | none => simp
          | some result =>
            cases result <;> simp
            split <;> simp

#print axioms evaluate_discard_call_no_loop_control
end InitECandidate.Runtime
