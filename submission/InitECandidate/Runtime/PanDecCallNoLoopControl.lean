import InitECandidate.Runtime.PanCallNoLoopControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A declaration-call can emit loop control only from its continuation,
never from its callee. Scope restoration does not change the result. -/
theorem evaluate_decCall_no_loop_control {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (tail : ∀ next : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState next continuation).1 ≠ some .break ∧
      (evaluateHOLFiniteState next continuation).1 ≠ some .continue) :
    (evaluateHOLFiniteState state (.decCall name shape function arguments continuation)).1 ≠ some .break ∧
    (evaluateHOLFiniteState state (.decCall name shape function arguments continuation)).1 ≠ some .continue := by
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
            | returned value =>
              simp only
              split
              · exact tail _
              · simp
            | error => simp
            | timeOut => simp
            | «break» => simp
            | «continue» => simp
            | exception exception value => simp
            | finalFfi ffi => simp

#print axioms evaluate_decCall_no_loop_control
end InitECandidate.Runtime
