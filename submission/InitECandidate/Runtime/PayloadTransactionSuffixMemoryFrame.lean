import InitECandidate.Runtime.PayloadTransactionHeaderWrites
import InitECandidate.Runtime.PayloadTransactionHeaderSuffixBound
import InitECandidate.Runtime.PayloadWithdrawalsMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The transaction-header stores and complete returned payload suffix
preserve every separated word and all allocator globals. -/
theorem payload_transaction_suffix_memory_frame {F : Type}
    (state post : PanSemStateFiniteExact 64 F)
    (payload array count withdrawals balance watched : BitVec 64) (value : ValueHOL 64)
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atList : state.locals.lookup (ofString "txs") = some (.rStruct [.val (.word array),.val (.word count)]))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (arrayDomain : state.memaddrs (payload + 32)) (countDomain : state.memaddrs (payload + 40))
    (separate : ∀ offset : BitVec 64, offset ∈ ([32,40,48,56,64,72,80,88,96,104,112,120,128] : List (BitVec 64)) →
      watched ≠ payload + offset)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 17) = (some (.returned value),post)) :
    post.memory watched = state.memory watched ∧ post.globals = state.globals := by
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
  have frame := payload_withdrawals_returned_memory_frame entry post payload withdrawals balance watched value
    pl wd bal (fun offset member => separate offset (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))) code run
  have at32 := separate 32 (by simp)
  have at40 := separate 40 (by simp)
  have storedFrame : entry.memory watched = state.memory watched := by
    change (if watched = payload + 40 then .word count else
      if watched = payload + 32 then .word array else state.memory watched) = state.memory watched
    rw [if_neg at40,if_neg at32]
  exact ⟨frame.1.trans storedFrame,frame.2⟩

#print axioms payload_transaction_suffix_memory_frame
end InitECandidate.Runtime
