import InitECandidate.Runtime.DiscardCallClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Caller locals do not affect a discarded call once argument values agree:
callee locals are installed afresh, and only caller-local restoration can differ. -/
theorem evaluate_discard_call_caller_locals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (argsBefore : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (argsAfter : evalListHOLFinite {state with locals := locals}
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,shape))
    (clock : state.clock ≠ 0) :
    let before := evaluateHOLFiniteState state (.call (some (none,none)) function arguments)
    let after := evaluateHOLFiniteState {state with locals := locals} (.call (some (none,none)) function arguments)
    (after.1,{after.2 with locals := before.2.locals}) = before := by
  dsimp only
  simp only [evaluateHOLFiniteState_call,argsBefore,argsAfter]
  rw [lookup]
  dsimp only
  simp only [if_neg clock]
  have sameEntry : callEntryStateHOLFinite {state with locals := locals} callee = callEntryStateHOLFinite state callee := rfl
  rw [sameEntry]
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
  | mk result post =>
      cases post
      cases result with
      | none => rfl
      | some result =>
          cases result <;> simp only
          all_goals first | rfl | (split <;> rfl)

#print axioms evaluate_discard_call_caller_locals
end InitECandidate.Runtime
