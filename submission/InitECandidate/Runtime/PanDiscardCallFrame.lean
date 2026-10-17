import InitECandidate.Runtime.DiscardCallClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A discarded handler-free call retains the callee's memory/global frame,
including zero-clock calls, all terminal outcomes and return-shape failures. -/
theorem evaluate_discard_call_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (bodyFrame : ∀ result post, evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post) →
      post.memory = state.memory ∧ post.globals = state.globals) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) function arguments)
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  by_cases zero : state.clock = 0
  · simp only [if_pos zero]
    exact ⟨rfl,rfl⟩
  · rw [if_neg zero]
    cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
    | mk result post =>
      have frame := bodyFrame result post run
      cases result with
      | none => exact frame
      | some result =>
        cases result <;> simp only
        all_goals first | exact frame | (split <;> exact frame)

#print axioms evaluate_discard_call_frame
end InitECandidate.Runtime
