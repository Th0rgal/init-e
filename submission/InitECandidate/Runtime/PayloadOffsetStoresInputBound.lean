import InitECandidate.Runtime.PayloadOffsetCheckInputBound
import InitECandidate.Runtime.PayloadOffsetStores
import InitECandidate.Runtime.TransactionDataScopedBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Installing the four offset-table words adds no ticks to the bound
for the original offset-check and complete remaining payload suffix. -/
theorem evaluate_payload_offset_stores_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer extra txs withdrawals balance heapPointer offsets length : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTxs : state.locals.lookup (ofString "o_txs") = some (.val (.word txs)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (budget : sszSplitBound length + 78 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 8)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + 78) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have stored := evaluate_payload_offset_stores state offsets extra txs withdrawals balance atOffsets
    atExtra atTxs atWithdrawals atBalance domain0 domain8 domain16 domain24
  let ready := journalRecordPost32 state offsets extra txs withdrawals balance
  have cells := payload_offset_stores_readback state offsets extra txs withdrawals balance
  have grouping : evaluateHOLFiniteState state (.seq payloadOffsetStores (payloadAt 12)) =
      evaluateHOLFiniteState state (payloadAt 8) := by
    rw [source_payload_offset_stores]
    unfold payloadOffsetStores
    rw [evaluate_seq_assoc]
    apply evaluate_seq_second_congr
    intro middle
    rw [evaluate_seq_assoc]
    apply evaluate_seq_second_congr
    intro next
    exact evaluate_seq_assoc next _ _ _
  rw [← grouping,evaluateHOLFiniteState_seq_line780,stored]
  have readExtra : memWord ready.memory offsets = extra := by
    have cell : ready.memory offsets = .word extra := by simpa using cells.1
    simp [memWord,cell]
  have readTxs : memWord ready.memory (offsets + 8) = txs := by unfold memWord; rw [cells.2.1]
  have readWithdrawals : memWord ready.memory (offsets + 16) = withdrawals := by unfold memWord; rw [cells.2.2.1]
  have readBalance : memWord ready.memory (offsets + 24) = balance := by unfold memWord; rw [cells.2.2.2]
  exact evaluate_payload_offset_check_input_bounded ready pointer extra txs withdrawals balance heapPointer offsets length
    atPointer atExtra atTxs atWithdrawals atBalance atLength atOffsets code heap pointerBound
    readExtra readTxs readWithdrawals readBalance budget

#print axioms evaluate_payload_offset_stores_input_bounded
end InitECandidate.Runtime
