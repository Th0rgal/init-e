import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A finite source body bound transfers through an ordinary call without a
result binding or exception handler, adding its one entry-clock step. -/
theorem evaluate_call_body_bound {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL) (bound : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,shape))
    (clock : state.clock ≠ 0)
    (cost : (callEntryStateHOLFinite state callee).clock ≤
      (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock + bound)
    (remaining : (evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body).2.clock ≤
      (callEntryStateHOLFinite state callee).clock) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).2.clock + bound + 1 ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).2.clock ≤ state.clock := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock]
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with
  | mk result post =>
    rw [run] at cost remaining
    dsimp only [callEntryStateHOLFinite] at cost remaining
    cases result with
    | none => simp_all; omega
    | some result =>
      cases result <;> simp_all [emptyLocalsHOLFinite] <;> (try split) <;> (try simp_all) <;> omega

#print axioms evaluate_call_body_bound
end InitECandidate.Runtime
