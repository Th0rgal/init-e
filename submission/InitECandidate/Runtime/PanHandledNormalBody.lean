import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A normal discard call whose handler cannot fall through exposes its real
returned callee execution and preserves that execution's global environment. -/
theorem evaluate_handled_normal_body {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (function handlerId handlerVar : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body handler : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (terminal : ∀ next : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState next handler).1 ≠ none)
    (run : evaluateHOLFiniteState state (.call (some (none,some (handlerId,handlerVar,handler))) function arguments) = (none,post)) :
    ∃ value output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),output) ∧
      post.globals = output.globals ∧ post.locals = state.locals := by
  rw [evaluateHOLFiniteState_call,args] at run
  simp only at run
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
          · refine ⟨value,output,rfl,?_,?_⟩
            all_goals rw [← (Prod.mk.inj run).2]
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

#print axioms evaluate_handled_normal_body
end InitECandidate.Runtime
