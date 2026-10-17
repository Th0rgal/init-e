import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A normal handler-free discard call exposes its actual returned callee
execution and preserves the global environment produced by that execution. -/
theorem evaluate_discard_normal_body_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post)) :
    ∃ value output, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),output) ∧
      post.memory = output.memory ∧ post.locals = state.locals := by
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
        | exception exceptionId value => cases run

#print axioms evaluate_discard_normal_body_memory
end InitECandidate.Runtime
