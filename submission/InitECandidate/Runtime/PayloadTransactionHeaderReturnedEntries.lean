import InitECandidate.Runtime.PayloadTransactionHeaderReturned
import InitECandidate.Runtime.PayloadWithdrawalsReturnedEntries
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original transaction header and withdrawal suffix export all three
variable-size hash entries together. -/
theorem payload_transaction_header_returned_entries {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (payload array count withdrawals balance input length : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atList : state.locals.lookup (ofString "txs") = some (.rStruct [.val (.word array),.val (.word count)]))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (atInput : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (arrayDomain : state.memaddrs (payload + 32)) (countDomain : state.memaddrs (payload + 40))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 17) = (some (.returned value),post)) :
    RlpSliceEntry post payload 2 array count ∧
      RlpSliceEntry post payload 3 (input + withdrawals) ((balance - withdrawals) / 44) ∧
      RlpSliceEntry post payload 4 (input + balance) (length - balance) := by
  have header := payload_transaction_header_returned state post payload array count withdrawals balance value
    atPayload atList atWithdrawals atBalance arrayDomain countDomain code run
  have metadata := evaluateHOLFiniteState_metadata state (payloadAt 17)
  rw [run] at metadata
  have grouping : evaluateHOLFiniteState state (payloadAt 17) =
      evaluateHOLFiniteState state (.seq payloadTransactionHeader (payloadAt 19)) := by
    rw [source_payload_transaction_header,← evaluate_seq_assoc]
    rfl
  have stores := evaluate_payload_transaction_header_writes state payload array count atPayload atList arrayDomain countDomain
  rw [grouping,evaluateHOLFiniteState_seq_line780,stores] at run
  dsimp only at run
  have entries := payload_withdrawals_returned_entries (payloadTransactionHeaderPost state payload array count) post
    payload input length withdrawals balance value atPayload atInput atLength atWithdrawals atBalance code run
  refine ⟨⟨?_,?_,?_,?_⟩,entries.2.2.1,entries.2.2.2⟩
  · rw [metadata.2.1]; exact arrayDomain
  · simpa [BitVec.add_assoc] using (metadata.2.1 ▸ countDomain)
  · exact header.1
  · simpa [BitVec.add_assoc] using header.2

#print axioms payload_transaction_header_returned_entries
end InitECandidate.Runtime
