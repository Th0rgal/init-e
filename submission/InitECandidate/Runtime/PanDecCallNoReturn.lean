import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A declaration-call can return a final value only through its continuation. -/
theorem evaluate_decCall_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (tail : ∀ next : PanSemStateFiniteExact 64 F, ∀ value : ValueHOL 64,
      (evaluateHOLFiniteState next continuation).1 ≠ some (.returned value)) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.decCall name shape function arguments continuation)).1 ≠ some (.returned value) := by
  rw [evaluateHOLFiniteState_decCall_total]
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
            cases result with
            | returned returnedValue =>
              simp only
              split
              · exact tail _ value
              · simp
            | error => simp
            | timeOut => simp
            | «break» => simp
            | «continue» => simp
            | exception exception exceptionValue => simp
            | finalFfi ffi => simp

#print axioms evaluate_decCall_no_return
end InitECandidate.Runtime
