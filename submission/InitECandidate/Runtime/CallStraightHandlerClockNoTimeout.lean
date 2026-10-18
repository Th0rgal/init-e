import InitECandidate.Runtime.CallBodyClockNoTimeout
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem evaluate_call_straight_handler_clock_no_timeout {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (function : MlS)
    (destination : Option (VarKind × MlS))
    (handlerId handlerVar : MlS) (handlerProgram : ProgHOL 64)
    (supported : straightLine handlerProgram = true)
    (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (result : Option (PanSemResultExact 64))
    (args : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some values)
    (lookup : lookupCodeHOLFinite state.code.lookup function values = some (body,callee,returnShape))
    (clock : state.clock ≠ 0)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body = (result,post))
    (noTimeout : result ≠ some .timeOut) :
    let output := evaluateHOLFiniteState state (.call (some (destination,some (handlerId,handlerVar,handlerProgram))) function arguments);
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
    case returned value =>
      split
      · cases destination with
        | none => simp
        | some destination =>
          rcases destination with ⟨kind,name⟩
          dsimp only
          split <;> cases kind <;> simp [setKvarHOLFinite,setVarHOLFinite,setGlobalHOLFinite]
      · simp
    case exception exceptionId value =>
      split
      · cases shape : state.eshapes.lookup handlerId with
        | none => simp
        | some shape =>
          dsimp only
          split
          · let resumed := setVarHOLFinite handlerVar value {post with locals := state.locals}
            have preserved := clockPreserving_of_straightLine handlerProgram supported resumed
            have noTimeout := evaluate_straightLine_no_timeout handlerProgram supported resumed
            exact ⟨noTimeout,preserved⟩
          · simp
      · simp

#print axioms evaluate_call_straight_handler_clock_no_timeout
end InitECandidate.Runtime
