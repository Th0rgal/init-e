import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- If its handler cannot fall through, a normally completed discard call
must have returned from the callee and restored the caller's local environment. -/
theorem evaluate_handled_normal_locals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (function handlerId handlerVar : MlS) (arguments : List (ExpHOL 64)) (handler : ProgHOL 64)
    (terminal : ∀ next : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState next handler).1 ≠ none)
    (run : evaluateHOLFiniteState state (.call (some (none,some (handlerId,handlerVar,handler))) function arguments) = (none,post)) :
    post.locals = state.locals := by
  rw [evaluateHOLFiniteState_call] at run
  cases args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none => rw [args] at run; cases run
  | some values =>
    rw [args] at run
    simp only at run
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => simp [lookup] at run
    | some data =>
      obtain ⟨body,callee,shape⟩ := data
      rw [lookup] at run
      simp only at run
      split at run
      · cases run
      · cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
        | mk result output =>
          rw [bodyRun] at run
          cases result with
          | none => cases run
          | some result =>
            cases result with
            | returned value =>
              simp only at run
              split at run
              · rw [← (Prod.mk.inj run).2]
              · cases run
            | error => cases run
            | timeOut => cases run
            | «break» => cases run
            | «continue» => cases run
            | finalFfi ffi => cases run
            | exception exceptionId value =>
              simp only at run
              split at run
              · cases declared : state.eshapes.lookup exceptionId with
                | none => simp [declared] at run
                | some kind =>
                  rw [declared] at run
                  simp only at run
                  split at run
                  · exact False.elim (terminal _ (Prod.mk.inj run).1)
                  · cases run
              · cases run

#print axioms evaluate_handled_normal_locals
end InitECandidate.Runtime
