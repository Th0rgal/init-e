import InitECandidate.Runtime.TrapCallClock
import InitECandidate.Runtime.TrapCallTerminal
import InitECandidate.Runtime.TrapCallNoTimeout
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every original conditional trap check either leaves its state
unchanged or exits exceptionally, at most one tick later. Expression failure,
zero flags and missing exception metadata are all included. -/
theorem evaluate_conditional_trap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (errorCode : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state
        (.ite condition (.call (some (none,none)) (ofString "trap_with") [.const errorCode]) .skip) = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → post = state) ∧ (∀ value, result ≠ some (.returned value)) := by
  rw [evaluateHOLFiniteState_ite]
  cases evaluated : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition with
  | none => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp⟩
  | some value =>
    cases value with
    | rStruct fields => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp⟩
    | nStruct name fields => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp⟩
    | val value =>
      cases value with
      | word flag =>
        by_cases zero : flag = 0
        · simp only [if_pos zero,evaluateHOLFiniteState_skip]
          exact ⟨none,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp⟩
        · simp only [if_neg zero]
          have clock := evaluate_trap_call_clock state (.const errorCode) errorCode code (by rfl)
          have terminal := evaluate_trap_call_terminal state (.const errorCode) errorCode code (by rfl)
          have safe := evaluate_trap_call_no_timeout state (.const errorCode) errorCode (by omega) code (by rfl)
          have noReturn := evaluate_discard_call_no_return state (ofString "trap_with") [.const errorCode]
          cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "trap_with") [.const errorCode]) with
          | mk result post =>
            rw [called] at clock terminal safe noReturn
            dsimp only at clock terminal safe noReturn
            cases result with
            | none => exact False.elim (terminal rfl)
            | some stopped =>
              exact ⟨some stopped,post,rfl,by omega,by omega,safe,by simp,noReturn⟩

#print axioms evaluate_conditional_trap_bounded
end InitECandidate.Runtime
