import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.PanDecCallContinuationBound
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A call to a straight callee consumes one clock, independently of argument
or return-shape failures. Its continuation may contain further bounded calls. -/
theorem evaluate_straightCallee_continuation_bounded {F : Type}
    (state : PanSemStateFiniteExact 64 F) (name function : MlS) (shape : ShapeHOL)
    (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailCost : Nat)
    (bodies : ∀ values body locals returnShape,
      lookupCodeHOLFinite state.code.lookup function values = some (body,locals,returnShape) → straightLine body = true)
    (tail : ∀ current : PanSemStateFiniteExact 64 F, current.code = state.code → tailCost ≤ current.clock →
      let evaluated := evaluateHOLFiniteState current continuation
      current.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ current.clock ∧
        evaluated.1 ≠ some .timeOut)
    (budget : 1 + tailCost ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.decCall name shape function arguments continuation)
    state.clock ≤ evaluated.2.clock + (1 + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  cases args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
  | none =>
    rw [evaluateHOLFiniteState_decCall_total,args]
    simp
  | some values =>
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none =>
      rw [evaluateHOLFiniteState_decCall_total,args]
      dsimp only
      rw [lookup]
      simp
    | some installed =>
      obtain ⟨body,callee,returnShape⟩ := installed
      let entry := callEntryStateHOLFinite state callee
      have supported := bodies values body callee returnShape lookup
      have clock := clockPreserving_of_straightLine body supported entry
      have safe := evaluate_straightLine_no_timeout body supported entry
      have metadata := evaluateHOLFiniteState_metadata entry body
      cases ran : evaluateHOLFiniteState entry body with
      | mk result post =>
        rw [ran] at clock safe metadata
        dsimp only at clock safe metadata
        have postCode : post.code = state.code := metadata.1
        have postClock : post.clock = state.clock - 1 := clock
        have positive : state.clock ≠ 0 := by omega
        have combined := evaluate_decCall_continuation_bounded state post name function shape returnShape
          arguments values body continuation callee result 1 tailCost args lookup positive ran
          (by change post.clock ≤ state.clock - 1; omega) (by omega) safe ?_
        · exact combined
        · intro value returned
          let resumed := setVarHOLFinite name value {post with locals := state.locals}
          exact tail resumed postCode (by change tailCost ≤ post.clock; omega)

#print axioms evaluate_straightCallee_continuation_bounded
end InitECandidate.Runtime
