import InitECandidate.Runtime.PanDiscardCallLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Observe a source result and every state component except caller locals. -/
def panOutputWithoutLocals {F : Type}
    (output : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F) :=
  (output.1,emptyLocalsHOLFinite output.2)

/-- Declaration-call locality reduces to argument agreement and locality of
its continuation after installing the returned local. No callee-body premise
is needed because both calls install identical fresh callee locals. -/
theorem evaluate_declaration_call_caller_locals {F : Type} (state : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (argsBefore : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (argsAfter : evalListHOLFinite {state with locals := locals}
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (transport : ∀ (post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64),
      panOutputWithoutLocals (evaluateHOLFiniteState (setVarHOLFinite name value {post with locals := locals}) continuation) =
      panOutputWithoutLocals (evaluateHOLFiniteState (setVarHOLFinite name value {post with locals := state.locals}) continuation)) :
    panOutputWithoutLocals (evaluateHOLFiniteState {state with locals := locals} (.decCall name shape function arguments continuation)) =
      panOutputWithoutLocals (evaluateHOLFiniteState state (.decCall name shape function arguments continuation)) := by
  simp only [evaluateHOLFiniteState_decCall_total,argsBefore,argsAfter]
  rw [lookup]
  dsimp only
  simp only [if_neg clock]
  have sameEntry : callEntryStateHOLFinite {state with locals := locals} callee = callEntryStateHOLFinite state callee := rfl
  rw [sameEntry]
  rw [fixClockHOLFinite_evaluateState]
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
  | mk result post =>
      cases result with
      | none => rfl
      | some result =>
          cases result with
          | returned value =>
              dsimp only
              split
              · exact transport post value
              · rfl
          | _ => rfl

#print axioms evaluate_declaration_call_caller_locals
end InitECandidate.Runtime
