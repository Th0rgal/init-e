import InitECandidate.Runtime.PayloadTransactionHeaderWrites
import InitECandidate.Runtime.PayloadTransactionHeaderSuffixBound
import InitECandidate.Runtime.PayloadWithdrawalsHeaderFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual transaction-header stores install the pointer and count that
survive withdrawal validation and the complete remaining payload suffix. -/
theorem payload_transaction_header_returned {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (payload array count withdrawals balance : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atList : state.locals.lookup (ofString "txs") = some (.rStruct [.val (.word array),.val (.word count)]))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (arrayDomain : state.memaddrs (payload + 32)) (countDomain : state.memaddrs (payload + 40))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 17) = (some (.returned value),post)) :
    post.memory (payload + 32) = .word array ∧ post.memory (payload + 40) = .word count := by
  have grouping : evaluateHOLFiniteState state (payloadAt 17) =
      evaluateHOLFiniteState state (.seq payloadTransactionHeader (payloadAt 19)) := by
    rw [source_payload_transaction_header,← evaluate_seq_assoc]
    rfl
  have stores := evaluate_payload_transaction_header_writes state payload array count atPayload atList arrayDomain countDomain
  rw [grouping,evaluateHOLFiniteState_seq_line780,stores] at run
  dsimp only at run
  let entry := payloadTransactionHeaderPost state payload array count
  have pl : entry.locals.lookup (ofString "pl") = some (.val (.word payload)) := atPayload
  have wd : entry.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)) := atWithdrawals
  have bal : entry.locals.lookup (ofString "o_bal") = some (.val (.word balance)) := atBalance
  have first := payload_withdrawals_returned_header_frame entry post payload withdrawals balance 32 value
    pl wd bal (by simp) code run
  have second := payload_withdrawals_returned_header_frame entry post payload withdrawals balance 40 value
    pl wd bal (by simp) code run
  have readback := payload_transaction_header_readback state payload array count
  exact ⟨first.trans readback.1,second.trans readback.2⟩

#print axioms payload_transaction_header_returned
end InitECandidate.Runtime
