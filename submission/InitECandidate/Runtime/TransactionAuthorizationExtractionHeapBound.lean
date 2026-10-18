import InitECandidate.Runtime.TransactionAuthorizationExtractionBound
import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.TxListItemAuthorizationCallHeapBound
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual authorization field extraction, decoding, result stores and index advance. -/
theorem evaluate_transaction_authorization_extraction_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame heapPointer : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (budget : txListItemAuthorizationCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionAuthorizationExtraction
    state.clock ≤ evaluated.2.clock + txListItemAuthorizationCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "k")] =
      some [.val (.word array),.val (.word index)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  rw [source_transaction_authorization_extraction,source_transaction_authorization_decode]
  exact evaluate_txListItem_authorization_call_heap_bounded state (ofString "aul") (ofString "au") _ transactionAuthorizationFinish (by rfl)
    array index input inputLength scratch frame heapPointer filled ceiling inputLimit args valid inside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap heapBound countLimit heapArena
    inputBeforeHeap inputBeforeFrame heapAbove heapAligned budget

#print axioms evaluate_transaction_authorization_extraction_heap_bounded
end InitECandidate.Runtime
