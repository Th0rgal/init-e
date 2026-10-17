import InitECandidate.Runtime.RlpFailReadFrame
import InitECandidate.Runtime.RlpFailCallBound
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every original RLP conditional error check either leaves its state
unchanged or exits exceptionally, at most one tick later. Expression failure,
zero flags and missing exception metadata are all included. -/
theorem evaluate_rlp_error_check {F : Type} (state : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (errorCode : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state
        (.ite condition (.call (some (none,none)) (ofString "rlp_fail") [.const errorCode]) .skip) = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → post = state) ∧ (∀ value, result ≠ some (.returned value)) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  rw [evaluateHOLFiniteState_ite]
  cases evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition with
  | none => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp,rfl,rfl⟩
  | some value =>
    cases value with
    | rStruct fields => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp,rfl,rfl⟩
    | nStruct name fields => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp,rfl,rfl⟩
    | val value =>
      cases value with
      | word flag =>
        by_cases zero : flag = 0
        · simp only [if_pos zero,evaluateHOLFiniteState_skip]
          exact ⟨none,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp,rfl,rfl⟩
        · simp only [if_neg zero]
          have bound := evaluate_rlpFail_call_bounded state (.const errorCode) errorCode code (by omega) (by rfl)
          have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const errorCode]
          have frame := evaluate_rlpFail_call_frame state (.const errorCode) errorCode code (by rfl)
          cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const errorCode]) with
          | mk result post =>
            rw [called] at bound noReturn frame
            dsimp only at bound noReturn frame
            cases result with
            | none => exact False.elim (bound.2.2 rfl)
            | some stopped =>
              exact ⟨some stopped,post,rfl,by omega,by omega,bound.2.1,by simp,noReturn,frame.1,frame.2⟩

#print axioms evaluate_rlp_error_check
end InitECandidate.Runtime
