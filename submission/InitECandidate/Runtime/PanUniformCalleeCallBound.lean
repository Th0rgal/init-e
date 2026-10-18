import InitECandidate.Runtime.CallBodyClockNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A uniform bound on every successfully bound callee also covers calls
whose arguments or function binding fail before entry. -/
theorem evaluate_uniformCallee_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (function : MlS) (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (bodyCost : Nat)
    (budget : bodyCost + 1 ≤ state.clock)
    (bodies : ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) →
      let entry := callEntryStateHOLFinite state locals
      let evaluated := evaluateHOLFiniteState entry body
      entry.clock ≤ evaluated.2.clock + bodyCost ∧ evaluated.2.clock ≤ entry.clock ∧
        evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) function arguments)
    state.clock ≤ evaluated.2.clock + (bodyCost + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_call,args]; simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_call,args]; dsimp only; rw [lookup]; simp
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      let entry := callEntryStateHOLFinite state callee
      have bounded := bodies values body callee returnShape lookup
      change entry.clock ≤ (evaluateHOLFiniteState entry body).2.clock + bodyCost ∧
        (evaluateHOLFiniteState entry body).2.clock ≤ entry.clock ∧
        (evaluateHOLFiniteState entry body).1 ≠ some .timeOut at bounded
      cases ran : evaluateHOLFiniteState entry body with
      | mk result post =>
        rw [ran] at bounded
        dsimp only at bounded
        have output := evaluate_call_body_clock_no_timeout state post function destination arguments values body callee
          returnShape result args lookup (by omega) ran bounded.2.2
        dsimp only
        rw [output.2]
        have spent : state.clock - 1 ≤ post.clock + bodyCost := bounded.1
        have kept : post.clock ≤ state.clock - 1 := bounded.2.1
        exact ⟨by omega,by omega,output.1⟩

#print axioms evaluate_uniformCallee_call_bounded
end InitECandidate.Runtime
