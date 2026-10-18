import InitECandidate.Runtime.ByteStraightLine
import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Calls into byte-writing straight-line bodies consume at most the entry
tick, uniformly over failed argument evaluation and return-shape checks. -/
theorem evaluate_byteStraightCallee_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (bodies : ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) → byteStraightLine body = true)
    (budget : 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)
    state.clock ≤ evaluated.2.clock + 1 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args]; simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      let entry := callEntryStateHOLFinite state callee
      have supported := bodies values body callee returnShape lookup
      have clock := clockPreserving_of_byteStraightLine body supported entry
      have safe := evaluate_byteStraightLine_no_timeout body supported entry
      cases ran : evaluateHOLFiniteState entry body with
      | mk result post =>
        rw [ran] at clock safe
        have output := evaluate_call_body_clock_no_timeout state post function destination arguments values body callee
          returnShape result args lookup (by omega) ran safe
        dsimp only
        rw [output.2]
        change post.clock = state.clock - 1 at clock
        exact ⟨by omega,by omega,output.1⟩

#print axioms evaluate_byteStraightCallee_call_bounded
end InitECandidate.Runtime
