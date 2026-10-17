import InitECandidate.Runtime.DiscardCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A normally completed handler-free call restores all caller locals. -/
theorem evaluate_discard_call_body_success_locals {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 = none) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).2.locals = state.locals := by
  rw [evaluateHOLFiniteState_call,args] at success ⊢
  dsimp only at success ⊢
  rw [lookup] at success ⊢
  dsimp only at success ⊢
  rw [if_neg clock,run] at success ⊢
  cases result with
  | none => cases success
  | some result =>
    cases result with
    | returned value =>
      dsimp only at success ⊢
      split at success
      · rename_i goodShape
        simp only [goodShape,if_true]
      · cases success
    | _ => cases success

/-- The caller-local result needs no argument, lookup or callee assumptions;
failed argument checks and zero-clock calls cannot satisfy normal completion. -/
theorem evaluate_discard_call_success_locals {F : Type}
    (state : PanSemStateFiniteExact 64 F) (function : MlS) (arguments : List (ExpHOL 64))
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 = none) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).2.locals = state.locals := by
  classical
  generalize args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = evaluated
  cases evaluated with
  | none => rw [evaluateHOLFiniteState_call,args] at success; cases success
  | some values =>
    generalize lookup : lookupCodeHOLFinite state.code.lookup function values = installed
    cases installed with
    | none => rw [evaluateHOLFiniteState_call,args] at success; dsimp only at success; rw [lookup] at success; cases success
    | some entry =>
      obtain ⟨body,callee,returnShape⟩ := entry
      by_cases zero : state.clock = 0
      · rw [evaluateHOLFiniteState_call,args] at success
        dsimp only at success
        rw [lookup] at success
        simp [zero] at success
      · exact evaluate_discard_call_body_success_locals state _ function arguments values body callee returnShape _ args lookup zero rfl success

#print axioms evaluate_discard_call_body_success_locals
#print axioms evaluate_discard_call_success_locals
end InitECandidate.Runtime
