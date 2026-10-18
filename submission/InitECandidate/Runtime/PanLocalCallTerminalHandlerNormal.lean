import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A successful assignment-form call followed by a normal continuation exposes
its checked callee return and resumes with the caller locals. -/
theorem evaluate_localCall_terminal_handler_normal_result {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body handler : ProgHOL 64) (handlerId handlerVar : MlS) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (terminal : ∀ current : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState current handler).1 ≠ none)
    (run : evaluateHOLFiniteState state
      (.call (some (some (.local,name),some (handlerId,handlerVar,handler))) function arguments) = (none,post)) :
    evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments) = (none,post) := by
  rw [evaluateHOLFiniteState_call,args] at run ⊢
  dsimp only at run ⊢
  rw [lookup] at run ⊢
  dsimp only at run ⊢
  by_cases zero : state.clock = 0
  · simp [zero] at run
  · rw [if_neg zero] at run ⊢
    cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result bodyPost =>
      rw [bodyRun] at run
      cases result with
      | none => cases run
      | some result =>
        cases result with
        | returned value => exact run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | finalFfi ffi => cases run
        | exception exception value =>
          dsimp only at run
          split at run
          · rename_i same
            subst exception
            cases shape : state.eshapes.lookup handlerId with
            | none => simp [shape] at run
            | some shape =>
              rw [shape] at run
              dsimp only at run
              split at run
              · have impossible := terminal (setVarHOLFinite handlerVar value {bodyPost with locals := state.locals})
                rw [run] at impossible
                exact False.elim (impossible rfl)
              · cases run
          · cases run

#print axioms evaluate_localCall_terminal_handler_normal_result
end InitECandidate.Runtime
