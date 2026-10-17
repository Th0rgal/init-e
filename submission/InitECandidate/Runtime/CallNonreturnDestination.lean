import InitECandidate.Runtime.DiscardCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- If the callee cannot return, a handler-free call's destination is never
assigned. Its exceptional execution is identical to a discarded call. -/
theorem evaluate_call_nonreturn_destination {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (noReturn : ∀ value, result ≠ some (.returned value)) :
    evaluateHOLFiniteState state (.call (some (destination,none)) function arguments) =
      evaluateHOLFiniteState state (.call (some (none,none)) function arguments) := by
  simp only [evaluateHOLFiniteState_call,args]
  simp only [lookup]
  simp only [if_neg clock,run]
  cases result with
  | none => rfl
  | some result => cases result <;> first | rfl | simp_all

#print axioms evaluate_call_nonreturn_destination
end InitECandidate.Runtime
