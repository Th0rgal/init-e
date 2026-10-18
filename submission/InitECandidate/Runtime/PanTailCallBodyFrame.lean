import InitECandidate.Runtime.ReadOnlyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Tail-call result checking and local cleanup preserve a callee memory/global frame. -/
theorem evaluate_tailCall_body_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (frame : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.memory = state.memory ∧
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.globals = state.globals) :
    (evaluateHOLFiniteState state (.call none function arguments)).2.memory = state.memory ∧
      (evaluateHOLFiniteState state (.call none function arguments)).2.globals = state.globals := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  split
  · exact ⟨rfl,rfl⟩
  · cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result post =>
      rw [run] at frame
      cases result with
      | none => exact frame
      | some result =>
        cases result <;> simp_all [emptyLocalsHOLFinite]
        all_goals split <;> simp_all [emptyLocalsHOLFinite]

#print axioms evaluate_tailCall_body_frame
end InitECandidate.Runtime
