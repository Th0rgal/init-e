import InitECandidate.Runtime.TransactionDecoderSource
import InitECandidate.Runtime.TxListItemBlobCallHeapBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual blob field extraction, decoding, result stores and index advance. -/
theorem evaluate_transaction_blob_extraction_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame heapPointer : BitVec 64) (filled ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : (index + 1#64).toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (budget : txListItemBlobCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state transactionBlobExtraction
    state.clock ≤ evaluated.2.clock + txListItemBlobCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.op .add [.var .local (ofString "k"),.const 1]] =
      some [.val (.word array),.val (.word (index + 1#64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_transaction_blob_extraction,source_transaction_blob_decode]
  exact evaluate_txListItem_blob_call_heap_bounded state (ofString "bl") (ofString "bh") _ transactionBlobFinish (by rfl)
    array (index + 1#64) input inputLength scratch frame heapPointer filled ceiling inputLimit args valid inside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap heapBound countLimit heapArena
    inputBeforeHeap inputBeforeFrame heapAbove budget

#print axioms evaluate_transaction_blob_extraction_heap_bounded
end InitECandidate.Runtime
