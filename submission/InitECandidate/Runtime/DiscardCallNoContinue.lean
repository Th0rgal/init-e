import InitECandidate.Runtime.DiscardCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A callee's loop-control result cannot escape a handler-free discard call. -/
theorem evaluate_discard_call_body_no_continue {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post)) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 ≠ some .continue := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock,run]
  cases result with
  | none => simp
  | some result =>
    cases result <;> simp_all
    split <;> simp

/-- This also holds when argument evaluation or code lookup fails, and at zero clock. -/
theorem evaluate_discard_call_no_continue {F : Type}
    (state : PanSemStateFiniteExact 64 F) (function : MlS) (arguments : List (ExpHOL 64)) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 ≠ some .continue := by
  classical
  generalize args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = evaluated
  cases evaluated with
  | none => rw [evaluateHOLFiniteState_call,args]; simp
  | some values =>
    generalize lookup : lookupCodeHOLFinite state.code.lookup function values = installed
    cases installed with
    | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
    | some entry =>
      obtain ⟨body,callee,returnShape⟩ := entry
      by_cases zero : state.clock = 0
      · rw [evaluateHOLFiniteState_call,args]
        dsimp only
        rw [lookup]
        simp [zero]
      · exact evaluate_discard_call_body_no_continue state _ function arguments values body callee returnShape _ args lookup zero rfl

#print axioms evaluate_discard_call_no_continue
#print axioms evaluate_discard_call_body_no_continue
end InitECandidate.Runtime
