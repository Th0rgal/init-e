import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A successful assignment-form call followed by a normal continuation exposes
its checked callee return and resumes with the caller locals. -/
theorem evaluate_localCall_normal_memory_scope {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,name),none)) function arguments) continuation) = (none,post)) :
    ∃ value bodyPost,
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),bodyPost) ∧
      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
      evaluateHOLFiniteState (setVarHOLFinite name value {bodyPost with locals := state.locals}) continuation = (none,post) := by
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call,args] at run
  dsimp only at run
  rw [lookup] at run
  dsimp only at run
  by_cases zero : state.clock = 0
  · simp [zero] at run
  · rw [if_neg zero] at run
    cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result bodyPost =>
      rw [bodyRun] at run
      cases result with
      | none => cases run
      | some result =>
        cases result with
        | returned value =>
          by_cases checked : shapeEqHOL (shapeOfHOLExact value) returnShape = true
          · simp only [checked,if_true] at run
            by_cases assignable : isValidValueHOLExact state.toExact .local name value = true
            · simp only [assignable,if_true] at run
              exact ⟨value,bodyPost,rfl,checked,run⟩
            · simp [assignable] at run
          · simp [checked] at run
        | error => cases run
        | timeOut => cases run
        | «break» => cases run
        | «continue» => cases run
        | exception exception value => cases run
        | finalFfi ffi => cases run

#print axioms evaluate_localCall_normal_memory_scope
end InitECandidate.Runtime
