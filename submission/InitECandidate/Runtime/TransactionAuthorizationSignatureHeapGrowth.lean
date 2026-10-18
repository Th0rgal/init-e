import InitECandidate.Runtime.TransactionAuthorizationReturnedHeapContract
import InitECandidate.Runtime.TransactionSignatureWitnessGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_authorization_signature_returned_heap_by_kind {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count tx kind input inputLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (valid : TransactionDecodeWitness state array count tx kind input inputLength scratch frame ceiling)
    (fields : valid.index.toNat + (if kind = 4#64 then 1 else 0) + 3 ≤ count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (countLimit : inputLimit * 120 < 2^64)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (headerBefore : tx.toNat + 376 < array.toNat)
    (reserve : valid.heap.toNat + inputLength.toNat * 248 ≤ frame.toNat)
    (budget : transactionAuthorizationSignatureCost inputLength.toNat ≤ state.clock)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedBelow : watchedArray.toNat + watchedCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (headerFits : tx.toNat + 376 < 2^64)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state transactionAuthorizationSignature = (some (.returned value),final)) :
    ∃ nextHeap : BitVec 64,
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      valid.heap.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ valid.heap.toNat + inputLength.toNat * 232 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  let tail := 3 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668)
  obtain ⟨post,tailRun,retained,next,indexEqual,lower,_,nextTicks,upper⟩ := transaction_authorization_returned_heap_contract state final
    array count tx kind input inputLength scratch frame ceiling inputLimit valid (by omega) inputBound limitBound
    orderedFrame framePositive scratchBelow countLimit arrayBelow (by omega) (inputLength.toNat * 16) tail
    (Nat.le_refl _) (by omega) budget watchedArray watchedCount watchedInput watchedLength watchedValid watchedBelow beforeTx value run
  have addOne : (valid.index + 1).toNat = valid.index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change valid.index.toNat + 1 < 2^64; omega)]
    rfl
  have nextFields : next.index.toNat + 3 ≤ count.toNat := by
    rw [indexEqual]
    split
    · rename_i selected
      rw [if_pos selected] at fields
      rw [addOne]; omega
    · rename_i skipped
      rw [if_neg skipped] at fields
      omega
  have globals := transaction_signature_witness_returned_globals post final array count tx kind input inputLength scratch frame ceiling inputLimit
    next nextFields headerBefore arrayBelow inputBound limitBound orderedFrame framePositive scratchBelow nextTicks
    watchedArray watchedCount watchedInput watchedLength retained watchedBelow beforeTx headerFits value tailRun
  exact ⟨next.heap,(globals _).trans next.heapGlobal,lower,upper,next.heapBound,next.heapAligned,
    (globals _).trans next.scratchGlobal,(globals _).trans next.frameGlobal⟩

#print axioms transaction_authorization_signature_returned_heap_by_kind
end InitECandidate.Runtime
