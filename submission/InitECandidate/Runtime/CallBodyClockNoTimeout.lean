import InitECandidate.Runtime.DiscardCallNoTimeout
import InitECandidate.Runtime.DiscardCallClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A handler-free call retains the body's final clock and cannot introduce
a timeout after a non-timeout body, for every return destination. -/
theorem evaluate_call_body_clock_no_timeout {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (noTimeout : result ≠ some .timeOut) :
    let output := evaluateHOLFiniteState state (.call (some (destination,none)) function arguments);
    output.1 ≠ some .timeOut ∧ output.2.clock = post.clock := by
  dsimp only
  rw [evaluateHOLFiniteState_call,args]
  dsimp only
  rw [lookup]
  dsimp only
  rw [if_neg clock,run]
  cases result with
  | none => simp
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split
    · cases destination with
      | none => simp
      | some destination =>
        rcases destination with ⟨kind,name⟩
        dsimp only
        split <;> cases kind <;> simp [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite]
    · simp

#print axioms evaluate_call_body_clock_no_timeout
end InitECandidate.Runtime
