import InitECandidate.Runtime.PayloadTransactionHeaderFrame
import InitECandidate.Runtime.PayloadWithdrawalsSuffixBound
import InitECandidate.Runtime.PanSeqAssoc
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both transaction-array header stores and the remaining original payload
suffix share the 67-tick bound, including header-store failures. -/
theorem evaluate_payload_transaction_header_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (withdrawals balance : BitVec 64)
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (code : state.code = originalRuntimeCode) (budget : 67 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 17)
    state.clock ≤ evaluated.2.clock + 67 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have grouping : evaluateHOLFiniteState state (payloadAt 17) =
      evaluateHOLFiniteState state (.seq payloadTransactionHeader (payloadAt 19)) := by
    rw [source_payload_transaction_header,← evaluate_seq_assoc]
    rfl
  have frame := evaluate_payload_transaction_header_frame state
  have metadata := evaluateHOLFiniteState_metadata state payloadTransactionHeader
  rw [grouping,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state payloadTransactionHeader with
  | mk result post =>
    rw [stored] at frame metadata
    dsimp only at frame metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by have ticks := frame.1; omega,by have ticks := frame.1; omega,frame.2.1⟩
    | none =>
      dsimp only
      have bounded := evaluate_payload_withdrawals_suffix_bounded post withdrawals balance
        ((frame.2.2.1 _).trans atWithdrawals) ((frame.2.2.1 _).trans atBalance)
        (metadata.1.trans code) (by rw [frame.1]; exact budget)
      exact ⟨by have spent := bounded.1; have ticks := frame.1; omega,
        by have remaining := bounded.2.1; have ticks := frame.1; omega,bounded.2.2⟩

#print axioms evaluate_payload_transaction_header_suffix_bounded
end InitECandidate.Runtime
