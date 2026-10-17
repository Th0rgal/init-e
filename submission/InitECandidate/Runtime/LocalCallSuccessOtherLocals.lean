import InitECandidate.Runtime.DiscardCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A successful assignment-form call preserves every caller local other
than its explicit destination. -/
theorem evaluate_local_call_body_success_other_locals {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function name : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (success : (evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments)).1 = none) :
    ∀ other : MlS, other ≠ name →
    (evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments)).2.locals.lookup other = state.locals.lookup other := by
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
        simp only [goodShape,if_true] at success ⊢
        split at success
        · rename_i assignable
          simp only [assignable,if_true]
          intro other different
          simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
        · cases success
      · cases success
    | _ => cases success

/-- The destination frame also covers arbitrary arguments and code lookups;
normal completion excludes failed checks and zero-clock calls. -/
theorem evaluate_local_call_success_other_locals {F : Type}
    (state : PanSemStateFiniteExact 64 F) (function name : MlS) (arguments : List (ExpHOL 64))
    (success : (evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments)).1 = none) :
    ∀ other : MlS, other ≠ name →
    (evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments)).2.locals.lookup other = state.locals.lookup other := by
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
      · exact evaluate_local_call_body_success_other_locals state _ function name arguments values body callee returnShape _ args lookup zero rfl success

#print axioms evaluate_local_call_body_success_other_locals
#print axioms evaluate_local_call_success_other_locals
end InitECandidate.Runtime
