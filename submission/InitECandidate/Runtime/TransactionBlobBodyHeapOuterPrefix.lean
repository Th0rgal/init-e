import InitECandidate.Runtime.TransactionBlobExtractionHeapOuterPrefix
import InitECandidate.Runtime.TransactionU256FieldBound
import InitECandidate.Runtime.TransactionU256FieldHeapOuterFrame
import InitECandidate.Runtime.PanSeqAssoc
set_option maxRecDepth 100000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original type-3 body includes scalar fee validation and blob-list decoding. -/
theorem transaction_blob_body_normal_heap_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : (index + 1#64).toNat < count.toNat)
    (middleInside : index.toNat < count.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 224 + 24 < array.toNat)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
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
    (budget : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat ≤ state.clock)
    (arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heapPointer.toNat)
    (headerBefore : tx.toNat + 264 < array.toNat)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeHeap : watchedArray.toNat + watchedCount.toNat * 16 ≤ heapPointer.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (run : evaluateHOLFiniteState state transactionBlobBody = (none,final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) transactionBlobFeeArguments =
      some [.val (.word array),.val (.word index),.val (.word (32 : BitVec 64))] := by
    simp [transactionBlobFeeArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  have firstBudget : cost ≤ state.clock := Nat.le_trans (Nat.le_add_right _ _) budget
  have bounded := evaluate_transaction_u256_field_bounded state (ofString "v")
    (.op .add [.var .local (ofString "tx"),.const 224]) transactionBlobFeeArguments
    array index 32 input inputLength scratch frame count.toNat ceiling inputLimit args valid middleInside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget
  change state.clock ≤ (evaluateHOLFiniteState state transactionBlobFeeField).2.clock + cost ∧
    (evaluateHOLFiniteState state transactionBlobFeeField).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state transactionBlobFeeField).1 ≠ some .timeOut at bounded
  rw [source_transaction_blob_body,← evaluate_seq_assoc] at run
  change evaluateHOLFiniteState state (.seq transactionBlobFeeField transactionBlobExtraction) = _ at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases firstRun : evaluateHOLFiniteState state transactionBlobFeeField with
  | mk result middle =>
    rw [firstRun] at run bounded
    dsimp only at bounded run
    cases result with
    | some result => cases run
    | none =>
      have kept := transaction_u256_field_normal_heap_outer_frame state middle tx 224 transactionBlobFeeArguments array index 32
        input inputLength scratch frame count ceiling inputLimit args valid middleInside inputBound limitBound scratchGlobal frameGlobal code
        orderedFrame framePositive scratchBelow arena firstBudget arrayFits arrayAbove txLocal before watchedArray watchedCount watchedInput watchedLength watchedValid (by omega) watchedAbove beforeTx firstRun
      have metadata := evaluateHOLFiniteState_metadata state transactionBlobFeeField
      rw [firstRun] at metadata
      exact transaction_blob_extraction_normal_heap_outer_prefix middle final array count index tx input inputLength scratch frame heapPointer ceiling inputLimit
        ((kept.2.2.2 _ (by decide)).trans arrayLocal) ((kept.2.2.2 _ (by decide)).trans indexLocal)
        ((kept.2.2.2 _ (by decide)).trans txLocal) kept.1 inside inputBound limitBound
        ((kept.2.2.1 _).trans scratchGlobal) ((kept.2.2.1 _).trans frameGlobal)
        (metadata.1.trans code) orderedFrame framePositive scratchBelow
        (by intro address lower upper; rw [metadata.2.1]; exact arena address lower upper)
        ((kept.2.2.1 _).trans heap) heapBound countLimit
        (by intro address lower upper; rw [metadata.2.1]; exact heapArena address lower upper)
        inputBeforeHeap inputBeforeFrame heapAbove arrayAbove arrayBeforeHeap watchedArray watchedCount watchedInput watchedLength kept.2.1 watchedAbove watchedBeforeHeap beforeTx
        (Nat.lt_trans headerBefore array.isLt) heapAligned
        (by have spent := bounded.1; change state.clock ≤ middle.clock + cost at spent; omega) run

#print axioms transaction_blob_body_normal_heap_outer_prefix
end InitECandidate.Runtime
