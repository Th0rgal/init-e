import InitECandidate.Runtime.PayloadExtraDataSuffixBound
import InitECandidate.Runtime.PayloadOffsetCheckReturned
import InitECandidate.Runtime.PayloadOffsetBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem sszSplitBound_slice_le (txs withdrawals length : BitVec 64)
    (ordered : txs.toNat ≤ withdrawals.toNat) (within : withdrawals.toNat ≤ length.toNat) :
    sszSplitBound (withdrawals - txs) ≤ sszSplitBound length := by
  have unsigned : txs ≤ withdrawals := ordered
  have difference := BitVec.toNat_sub_of_le unsigned
  unfold sszSplitBound
  rw [difference]
  omega

/-- Offset checking, extra-data validation, variable-list decoding and the
remaining withdrawal/header tail are bounded together, for every outcome. -/
theorem evaluate_payload_offset_check_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (readExtra : memWord state.memory offsets = extra)
    (readTxs : memWord state.memory (offsets + 8) = txs)
    (readWithdrawals : memWord state.memory (offsets + 16) = withdrawals)
    (readBalance : memWord state.memory (offsets + 24) = balance)
    (budget : sszSplitBound length + 78 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 12)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + 78) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have callBound := evaluate_payload_offset_check_call_bounded state offsets length atOffsets atLength code (by omega)
  have metadata := evaluateHOLFiniteState_metadata state payloadOffsetCheckCall
  rw [source_payload_offset_check,evaluateHOLFiniteState_seq_line780]
  cases checked : evaluateHOLFiniteState state payloadOffsetCheckCall with
  | mk result middle =>
    rw [checked] at callBound metadata
    dsimp only at callBound metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by have consumed := callBound.1; omega,callBound.2.1,callBound.2.2⟩
    | none =>
      dsimp only
      obtain ⟨_,first,accepted,memory,globals,domain,locals⟩ :=
        payload_offset_check_returned state middle offsets length atOffsets atLength code checked
      obtain ⟨_,_,ordered,wdBal,balLength⟩ := payload_offset_bounds state offsets length extra txs withdrawals balance
        first accepted readExtra readTxs readWithdrawals readBalance
      have sliceBound := sszSplitBound_slice_le txs withdrawals length ordered (by omega)
      have tail := evaluate_payload_extra_data_suffix_bounded middle pointer extra txs withdrawals balance heapPointer
        (by rw [locals]; exact atPointer) (by rw [locals]; exact atExtra) (by rw [locals]; exact atTxs)
        (by rw [locals]; exact atWithdrawals) (by rw [locals]; exact atBalance) (metadata.1.trans code)
        (by rw [globals]; exact heap) pointerBound (by have consumed := callBound.1; omega)
      exact ⟨by have consumed := callBound.1; have after := tail.1; omega,
        by have remaining := callBound.2.1; have after := tail.2.1; omega,tail.2.2⟩

#print axioms sszSplitBound_slice_le
#print axioms evaluate_payload_offset_check_input_bounded
end InitECandidate.Runtime
