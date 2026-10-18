import InitECandidate.Runtime.PanLocalCallNormalMemoryScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A normal assignment call exposes the actual checked return and exact resumed state. -/
theorem evaluate_localCall_normal_result {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments) = (none,post)) :
    ∃ value bodyPost,
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (some (.returned value),bodyPost) ∧
      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
      post = setVarHOLFinite name value {bodyPost with locals := state.locals} := by
  have sequence : evaluateHOLFiniteState state
      (.seq (.call (some (some (.local,name),none)) function arguments) .skip) = (none,post) := by
    rw [evaluateHOLFiniteState_seq_line780,run]
    exact evaluateHOLFiniteState_skip post
  obtain ⟨value,bodyPost,bodyRun,checked,tail⟩ := evaluate_localCall_normal_memory_scope state post name function
    returnShape arguments values body .skip callee args lookup sequence
  rw [evaluateHOLFiniteState_skip] at tail
  exact ⟨value,bodyPost,bodyRun,checked,(Prod.mk.inj tail).2.symm⟩

#print axioms evaluate_localCall_normal_result
end InitECandidate.Runtime
