import InitECandidate.Runtime.TransactionAccessReturnedHeapContract
import InitECandidate.Runtime.TransactionBlobSignatureHeapGrowth
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_typed_signature_returned_heap_by_kind {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 0#64 then 0 else 1) + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 3 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 376 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 7 ≤ frame.toNat)
    (budget : transactionTypedSignatureCost inputLength.toNat ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBelow : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (headerFits : tx.toNat + 376 < 2^64)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionTypedSignature = (some (.returned value),final)) :
    ∃ nextHeap : BitVec 64,
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      valid.heap.toNat ≤ nextHeap.toNat ∧
      nextHeap.toNat ≤ valid.heap.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 280 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  obtain ⟨post,tailRun,retained,next,indexEqual,lower,space,nextTicks,upper⟩ := transaction_access_returned_heap_contract state final
    array count tx kind input inputLength scratch frame ceiling inputLimit valid (by omega) inputBound limitBound
    orderedFrame framePositive scratchBelow (by omega) arrayBelow (by omega) (inputLength.toNat * 296 + 7)
    (transactionBlobSignatureCost inputLength.toNat) (by omega) (by omega) budget
    watchedArray watchedCount watchedInput watchedLength watchedValid watchedBelow beforeTx value run
  have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have nextFields : next.index.toNat + (if kind = 3#64 then 2 else 0) + (if kind = 4#64 then 1 else 0) + 3 ≤ count.toNat := by
    rw [indexEqual]
    split
    · rename_i skipped
      rw [if_pos skipped] at fields
      omega
    · rename_i selected
      rw [if_neg selected] at fields
      rw [addOne]; omega
  obtain ⟨nextHeap,binding,tailLower,tailUpper,heapBound,aligned,scratchFinal,frameFinal⟩ := transaction_blob_signature_returned_heap_by_kind post final array count tx kind input inputLength scratch frame ceiling inputLimit
    next nextFields inputBound limitBound orderedFrame framePositive scratchBelow countLimit arrayBelow headerBefore (by omega) nextTicks
    watchedArray watchedCount watchedInput watchedLength retained watchedBelow beforeTx headerFits value tailRun
  exact ⟨nextHeap,binding,lower.trans tailLower,by omega,heapBound,aligned,scratchFinal,frameFinal⟩

#print axioms transaction_typed_signature_returned_heap_by_kind
end InitECandidate.Runtime
