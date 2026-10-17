import InitECandidate.Runtime.RlpFailCallTerminal
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Without any clock premise, a passing RLP check leaves the full state
unchanged, and no conditional error check can return a parsed value. -/
theorem evaluate_rlp_error_check_flow {F : Type} (state : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (errorCode : BitVec 64) (code : state.code = originalRuntimeCode) :
    ∃ result post, evaluateHOLFiniteState state
        (.ite condition (.call (some (none,none)) (ofString "rlp_fail") [.const errorCode]) .skip) = (result,post) ∧
      (result = none → post = state) ∧ (∀ value, result ≠ some (.returned value)) := by
  rw [evaluateHOLFiniteState_ite]
  cases evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition with
  | none => exact ⟨some .error,state,rfl,by simp,by intro value; simp⟩
  | some value =>
    cases value with
    | rStruct fields => exact ⟨some .error,state,rfl,by simp,by intro value; simp⟩
    | nStruct name fields => exact ⟨some .error,state,rfl,by simp,by intro value; simp⟩
    | val value =>
      cases value with
      | word flag =>
        by_cases zero : flag = 0
        · simp only [if_pos zero,evaluateHOLFiniteState_skip]
          exact ⟨none,state,rfl,by simp,by intro value; simp⟩
        · simp only [if_neg zero]
          have terminal := evaluate_rlpFail_call_terminal state (.const errorCode) errorCode code (by rfl)
          have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const errorCode]
          cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const errorCode]) with
          | mk result post =>
            rw [run] at terminal noReturn
            exact ⟨result,post,rfl,(by intro normal; exact False.elim (terminal normal)),noReturn⟩

#print axioms evaluate_rlp_error_check_flow
end InitECandidate.Runtime
