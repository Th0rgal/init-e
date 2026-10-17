import InitECandidate.Runtime.RlpReadLengthAfterCheck
import InitECandidate.Runtime.RlpFailCallBound
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpReadLengthCheck : ExpHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_read_length with
  | .seq (.ite condition _ _) _ => condition
  | _ => .const 0

theorem source_rlpReadLength_body : sourceFunctionBody Guest.guestFn_rlp_read_length =
    .seq (.ite rlpReadLengthCheck (.call (some (none,none)) (ofString "rlp_fail") [.const 2]) .skip)
      rlpReadLengthAfterCheck := by
  simp only [rlpReadLengthCheck,rlpReadLengthAfterCheck,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- All initial canonicality-check outcomes and all byte reads are included
in the original function's source-clock bound. No readability premise is needed. -/
theorem evaluate_rlpReadLength_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : length.toNat + 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_read_length) = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat + 1) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ word : BitVec 64, value = .val (.word word)) := by
  rw [source_rlpReadLength_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  cases condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) rlpReadLengthCheck with
  | none => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by intro value impossible; cases impossible⟩
  | some value =>
    cases value with
    | rStruct fields => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by intro value impossible; cases impossible⟩
    | nStruct name fields => exact ⟨some .error,state,rfl,by omega,by omega,by simp,by intro value impossible; cases impossible⟩
    | val value =>
      cases value with
      | word flag =>
        by_cases zero : flag = 0
        · simp only [if_pos zero,evaluateHOLFiniteState_skip]
          obtain ⟨result,post,run,cost,remaining,noTimeout,returned⟩ :=
            evaluate_rlpReadLength_after_check_bounded state pointer length pointerLocal lengthLocal (by omega)
          exact ⟨result,post,run,by omega,remaining,noTimeout,returned⟩
        · simp only [if_neg zero]
          have bound := evaluate_rlpFail_call_bounded state (.const 2) 2 code (by omega) (by rfl)
          have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 2]
          cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 2]) with
          | mk result post =>
            rw [called] at bound noReturn
            dsimp only at bound noReturn
            cases result with
            | none => exact False.elim (bound.2.2 rfl)
            | some stopped =>
              refine ⟨some stopped,post,rfl,by omega,by omega,bound.2.1,?_⟩
              intro value returned
              exact False.elim (noReturn value returned)

#print axioms evaluate_rlpReadLength_body_bounded
end InitECandidate.Runtime
