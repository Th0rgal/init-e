import InitECandidate.Runtime.PayloadOffsetCheckSuffixBound
import InitECandidate.Runtime.PayloadOffsetStores
import InitECandidate.Runtime.TransactionDataScopedBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Installing the four offset-table words adds no ticks to the bound
for the original offset-check and complete remaining payload suffix. -/
theorem evaluate_payload_offset_stores_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (budget : sszSplitBound (withdrawals - txs) + 78 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 8)
    state.clock ≤ evaluated.2.clock + (sszSplitBound (withdrawals - txs) + 78) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ticks := clockPreserving_of_straightLine payloadOffsetStores (by rfl) state
  have noTimeout := evaluate_straightLine_no_timeout payloadOffsetStores (by rfl) state
  have locals := fun key => evaluate_straight_local_frame key payloadOffsetStores (by rfl) state
  have globals := fun key => evaluate_avoidsGlobalAssignment key payloadOffsetStores (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state payloadOffsetStores
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
  rw [← grouping,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state payloadOffsetStores with
  | mk result middle =>
    rw [stored] at ticks noTimeout locals globals metadata
    dsimp only at ticks noTimeout locals globals metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,by omega,noTimeout⟩
    | none =>
      dsimp only
      have tail := evaluate_payload_offset_check_suffix_bounded middle pointer extra txs withdrawals balance heapPointer offsets length
        ((locals _).trans atPointer) ((locals _).trans atExtra) ((locals _).trans atTxs)
        ((locals _).trans atWithdrawals) ((locals _).trans atBalance) ((locals _).trans atLength)
        ((globals _).trans atOffsets) (metadata.1.trans code) ((globals _).trans heap) pointerBound
        (by rw [ticks]; exact budget)
      exact ⟨by have consumed := tail.1; omega,by have remaining := tail.2.1; omega,tail.2.2⟩

#print axioms evaluate_payload_offset_stores_suffix_bounded
end InitECandidate.Runtime
