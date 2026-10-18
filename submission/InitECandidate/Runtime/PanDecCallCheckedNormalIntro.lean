import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Reconstruct the exact declaration result from a checked callee return and normal continuation. -/
theorem evaluate_decCall_checked_normal_intro {F : Type}
    (state bodyPost output : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (value : ValueHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (nonzero : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (PanSemResultExact.returned value),bodyPost))
    (checked : shapeEqHOL (shapeOfHOLExact value) shape = true ∧ shapeEqHOL (shapeOfHOLExact value) returnShape = true)
    (tailRun : evaluateHOLFiniteState (setVarHOLFinite name value {bodyPost with locals := state.locals}) continuation = (none,output)) :
    evaluateHOLFiniteState state (.decCall name shape function arguments continuation) =
      (none,{output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)}) := by
  have remaining := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite state callee) body
  rw [run] at remaining
  have fixed : fixClockHOLFinite (callEntryStateHOLFinite state callee) (some (PanSemResultExact.returned value),bodyPost) =
      (some (PanSemResultExact.returned value),bodyPost) := by
    simp [fixClockHOLFinite,Nat.not_lt.mpr remaining]
  rw [evaluateHOLFiniteState_decCall_total,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,run,fixed]
  dsimp only
  rw [checked.1,checked.2]
  rw [tailRun]
  rfl

#print axioms evaluate_decCall_checked_normal_intro
end InitECandidate.Runtime
