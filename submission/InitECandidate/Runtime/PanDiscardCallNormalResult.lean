import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A normally completed discard call exposes its checked body return and
exact caller-local restoration. -/
theorem evaluate_discardCall_normal_result {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) function arguments) = (none,post)) :
    ∃ value bodyPost,
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),bodyPost) ∧
      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
      post = {bodyPost with locals := state.locals} := by
  rw [evaluateHOLFiniteState_call,args] at run
  dsimp only at run
  rw [lookup] at run
  dsimp only at run
  by_cases zero : state.clock = 0
  · simp [zero] at run
  · rw [if_neg zero] at run
    cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result middle =>
      rw [bodyRun] at run
      cases result with
      | none => simp at run
      | some result =>
        cases result <;> simp only at run
        case returned value =>
          split at run
          · rename_i checked
            exact ⟨value,middle,rfl,checked,(Prod.mk.inj run).2.symm⟩
          · simp at run
        all_goals simp at run

#print axioms evaluate_discardCall_normal_result
end InitECandidate.Runtime
