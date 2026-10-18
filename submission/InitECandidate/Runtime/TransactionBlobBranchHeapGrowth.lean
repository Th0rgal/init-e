import InitECandidate.Runtime.TransactionBlobBodyHeapGrowth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original type-3 body includes scalar fee validation and blob-list decoding. -/
theorem transaction_blob_branch_normal_heap_growth {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : (index + 1#64).toNat < count.toNat)
    (middleInside : index.toNat < count.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (before : tx.toNat + 224 + 24 < array.toNat)
    (arrayBelow : array.toNat + count.toNat * 16 ≤ frame.toNat)
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
    (heapBeforeFrame : heapPointer.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (budget : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668) + txListItemBlobCost inputLength.toNat ≤ state.clock)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (run : evaluateHOLFiniteState state transactionBlobBranch = (none,final)) :
    ∃ nextHeap : BitVec 64,
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      heapPointer.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ heapPointer.toNat + inputLength.toNat * 48 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 := by
  rw [source_transaction_blob_branch,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      have equal := (Prod.mk.inj run).2
      subst final
      exact ⟨heapPointer,heap,Nat.le_refl _,by omega,heapBound,heapAligned⟩
    · exact transaction_blob_body_normal_heap_growth state final array count index tx input inputLength scratch frame heapPointer ceiling inputLimit
        arrayLocal indexLocal valid inside middleInside txLocal before arrayBelow inputBound limitBound scratchGlobal frameGlobal code
        orderedFrame framePositive scratchBelow arena heap heapBound countLimit heapArena inputBeforeHeap heapBeforeFrame budget
        heapAligned run
  · cases run

#print axioms transaction_blob_branch_normal_heap_growth
end InitECandidate.Runtime
