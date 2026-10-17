import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A handled discard call cannot return a final value if its handler cannot;
its callee's returned value is consumed by the discard-call semantics. -/
theorem evaluate_handled_discard_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function handlerId handlerVar : MlS) (arguments : List (ExpHOL 64)) (handler : ProgHOL 64)
    (handlerNoReturn : ∀ next : PanSemStateFiniteExact 64 F, ∀ value : ValueHOL 64,
      (evaluateHOLFiniteState next handler).1 ≠ some (.returned value)) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.call (some (none,some (handlerId,handlerVar,handler))) function arguments)).1 ≠ some (.returned value) := by
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => simp
  | some values =>
    simp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => simp
    | some data =>
      obtain ⟨body,callee,shape⟩ := data
      simp only
      split
      · simp
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
        | mk result output =>
          cases result with
          | none => simp
          | some result =>
            cases result with
            | returned returnedValue => simp only; split <;> simp
            | error => simp
            | timeOut => simp
            | «break» => simp
            | «continue» => simp
            | finalFfi ffi => simp
            | exception exceptionId exceptionValue =>
              simp only
              split
              · cases declared : state.eshapes.lookup exceptionId with
                | none => simp
                | some kind =>
                  simp only
                  split
                  · exact handlerNoReturn _ value
                  · simp
              · simp

#print axioms evaluate_handled_discard_no_return
end InitECandidate.Runtime
