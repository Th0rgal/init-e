import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Handler-free assignment/discard calls consume callee returns and reject
callee loop control; these values never escape into an enclosing loop. -/
theorem evaluate_handlerFree_call_control {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (function : MlS) (arguments : List (ExpHOL 64)) :
    (evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)).1 ≠ some .break ∧
    (evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)).1 ≠ some .continue ∧
    (∀ value, (evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)).1 ≠ some (.returned value)) := by
  rw [evaluateHOLFiniteState_call]
  cases argsRun : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
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
            split
            · cases destination with
              | none => simp
              | some destination =>
                obtain ⟨kind,name⟩ := destination
                dsimp only
                split <;> simp
            · simp

#print axioms evaluate_handlerFree_call_control
end InitECandidate.Runtime
