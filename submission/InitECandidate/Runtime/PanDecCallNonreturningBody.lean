import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A declaration-call cannot run its continuation when the actual callee
cannot return; malformed callee control is also converted to terminal error. -/
theorem evaluate_decCall_nonreturning_body_control {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (noReturn : ∀ value, (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).1 ≠ some (.returned value)) :
    (evaluateHOLFiniteState state (.decCall name shape function arguments continuation)).1 ≠ none ∧
    (∀ value, (evaluateHOLFiniteState state (.decCall name shape function arguments continuation)).1 ≠ some (.returned value)) := by
  rw [evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  by_cases zero : state.clock = 0
  · simp [zero]
  · rw [if_neg zero]
    cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result post =>
      cases result with
      | none => simp
      | some result =>
        cases result <;> simp_all

#print axioms evaluate_decCall_nonreturning_body_control
end InitECandidate.Runtime
