import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual arbitrary-argument declaration calls only resume after real shape checks. -/
theorem runBounded_checked_declaration {F : Type} (state : PanSemStateFiniteExact 64 F)
 (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
 (bodyCost tailCost : Nat) (budget : bodyCost+1+tailCost≤state.clock)
 (bodies : ∀values body callee returnShape,
  evalListHOLFinite state (h:=fun a=>Classical.propDecidable (state.memaddrs a)) arguments=some values→
  lookupCodeHOLFinite state.code.lookup function values=some (body,callee,returnShape)→
  RunBounded (callEntryStateHOLFinite state callee) body bodyCost ∧
  ∀value post,evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body=(some (.returned value),post)→
   (shapeEqHOL (shapeOfHOLExact value) shape && shapeEqHOL (shapeOfHOLExact value) returnShape)=true→
   tailCost≤post.clock→RunBounded (setVarHOLFinite name value {post with locals:=state.locals}) continuation tailCost) :
 RunBounded state (.decCall name shape function arguments continuation) (bodyCost+1+tailCost) := by
 cases args : evalListHOLFinite state (h:=fun a=>Classical.propDecidable (state.memaddrs a)) arguments with
 | none=>
  unfold RunBounded
  rw [evaluateHOLFiniteState_decCall_total,args]
  simp
 | some values=>
  cases lookup : lookupCodeHOLFinite state.code.lookup function values with
  | none=>
   unfold RunBounded
   rw [evaluateHOLFiniteState_decCall_lookup_none state name shape function arguments continuation values args lookup]
   simp
  | some data=>
   obtain ⟨body,callee,returnShape⟩:=data
   obtain ⟨bounded,resume⟩:=bodies values body callee returnShape args lookup
   cases ran : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
   | mk result post=>
    unfold RunBounded at bounded
    rw [ran] at bounded
    have whole:=evaluate_decCall_checked_continuation_bounded state post name function shape returnShape arguments values
     body continuation callee result (bodyCost+1) tailCost args lookup (by omega) ran bounded.2.1 (by have spent:=bounded.1;change state.clock-1≤post.clock+bodyCost at spent;omega) bounded.2.2 (by
      intro value returned checked
      subst returned
      exact resume value post ran checked (by have spent:=bounded.1;change state.clock-1≤post.clock+bodyCost at spent;omega))
    exact whole
#print axioms runBounded_checked_declaration
end InitECandidate.Runtime
