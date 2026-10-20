import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.PanHandledCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- A concrete call-entry body bound composes with the actual handler. Shape
failures and unmatched exceptions are included; no returned/normal premise. -/
theorem RunBounded.handledCall {F : Type} (s : PanSemStateFiniteExact 64 F)
    (function handlerId handlerVar : MlS) (destination : Option (VarKind × MlS))
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body handler : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (bodyCost handlerCost : Nat)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments=some values)
    (lookup : lookupCodeHOLFinite s.code.lookup function values=some (body,callee,returnShape))
    (code : s.code=originalRuntimeCode) (budget : bodyCost+1+handlerCost≤s.clock)
    (bounded : RunBounded (callEntryStateHOLFinite s callee) body bodyCost)
    (handlerBounded : ProgBounded handler handlerCost) :
    RunBounded s (.call (some (destination,some (handlerId,handlerVar,handler))) function arguments) (bodyCost+1+handlerCost) := by
  have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
  | mk result post =>
    unfold RunBounded at bounded
    rw [run] at bounded metadata
    have spent : s.clock≤post.clock+(bodyCost+1) := by
      have h:=bounded.1
      change s.clock-1≤post.clock+bodyCost at h
      omega
    have remaining : post.clock≤s.clock := by
      have h:=bounded.2.1
      change post.clock≤s.clock-1 at h
      omega
    have output := evaluate_handled_call_bounded s post function handlerId handlerVar destination arguments values body handler callee
      returnShape result (bodyCost+1) handlerCost args lookup (by omega) run spent remaining bounded.2.2 (by
        intro value exceptionRun
        apply handlerBounded
        · exact metadata.1.trans code
        · change handlerCost≤post.clock
          omega)
    exact output
#print axioms RunBounded.handledCall
end InitECandidate.Runtime
