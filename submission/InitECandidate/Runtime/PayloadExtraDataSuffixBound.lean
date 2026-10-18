import InitECandidate.Runtime.PayloadExtraDataHeader
import InitECandidate.Runtime.PayloadSplitSuffixBound
import InitECandidate.Runtime.StraightLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The two extra-data header stores add no source ticks and retain the
bindings needed by the complete bounded list/withdrawal suffix. -/
theorem evaluate_payload_extra_data_stores_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer txs withdrawals balance heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atTxs : state.locals.lookup (ofString "o_txs") = some (.val (.word txs)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496)
    (budget : sszSplitBound (withdrawals - txs) + 68 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 14)
    state.clock ≤ evaluated.2.clock + (sszSplitBound (withdrawals - txs) + 68) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have ticks := clockPreserving_of_straightLine payloadExtraDataHeader (by rfl) state
  have noTimeout := evaluate_straightLine_no_timeout payloadExtraDataHeader (by rfl) state
  have locals := fun key => evaluate_straight_local_frame key payloadExtraDataHeader (by rfl) state
  have globals := evaluate_avoidsGlobalAssignment (ofString "heap_ptr") payloadExtraDataHeader (by rfl) state
  have metadata := evaluateHOLFiniteState_metadata state payloadExtraDataHeader
  rw [evaluate_payload_extra_data_header_source,evaluateHOLFiniteState_seq_line780]
  cases stored : evaluateHOLFiniteState state payloadExtraDataHeader with
  | mk result middle =>
    rw [stored] at ticks noTimeout locals globals metadata
    dsimp only at ticks noTimeout locals globals metadata ⊢
    cases result with
    | some result =>
      dsimp only
      exact ⟨by omega,by omega,noTimeout⟩
    | none =>
      dsimp only
      have tail := evaluate_payload_split_suffix_bounded middle pointer txs withdrawals balance heapPointer
        ((locals _).trans atPointer) ((locals _).trans atTxs) ((locals _).trans atWithdrawals)
        ((locals _).trans atBalance) (metadata.1.trans code) (globals.trans heap) pointerBound
        (by rw [ticks]; exact budget)
      exact ⟨by have consumed := tail.1; omega,by have remaining := tail.2.1; omega,tail.2.2⟩

/-- The extra-data guard and all remaining original payload work share the
list-size bound. The rejecting guard branch is included. -/
theorem evaluate_payload_extra_data_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer extra txs withdrawals balance heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atExtra : state.locals.lookup (ofString "o_extra") = some (.val (.word extra)))
    (atTxs : state.locals.lookup (ofString "o_txs") = some (.val (.word txs)))
    (atWithdrawals : state.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)))
    (atBalance : state.locals.lookup (ofString "o_bal") = some (.val (.word balance)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496)
    (budget : sszSplitBound (withdrawals - txs) + 68 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 13)
    state.clock ≤ evaluated.2.clock + (sszSplitBound (withdrawals - txs) + 68) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases oversized : (32 : BitVec 64) < txs - extra
  · have rejected := evaluate_payload_extra_data_rejection_bounded state extra txs atExtra atTxs oversized code (by omega)
    exact ⟨by have consumed := rejected.1; omega,rejected.2.1,rejected.2.2.1⟩
  · rw [source_payload_extra_data_guard,evaluateHOLFiniteState_seq_line780,
      evaluate_payload_extra_data_guard state extra txs atExtra atTxs,if_neg oversized]
    exact evaluate_payload_extra_data_stores_suffix_bounded state pointer txs withdrawals balance heapPointer
      atPointer atTxs atWithdrawals atBalance code heap pointerBound budget

#print axioms evaluate_payload_extra_data_stores_suffix_bounded
#print axioms evaluate_payload_extra_data_suffix_bounded
end InitECandidate.Runtime
