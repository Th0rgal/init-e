import InitECandidate.Runtime.DiscardCallClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A call with discarded return value and no exception handler retains the
callee's clock for every result, including exceptions and external termination. -/
theorem evaluate_discard_call_body_terminal {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (noReturn : ∀ value, result ≠ some (.returned value)) :
    (evaluateHOLFiniteState state (.call (some (none,none)) function arguments)).1 ≠ none := by
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock,run]
  cases result with
  | none => simp
  | some result =>
    cases result <;> simp_all

#print axioms evaluate_discard_call_body_terminal
end InitECandidate.Runtime
