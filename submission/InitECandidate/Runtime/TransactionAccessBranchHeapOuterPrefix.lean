import InitECandidate.Runtime.TransactionAccessExtractionHeapOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Executing or skipping the actual access-list conditional retains transaction slices. -/
theorem transaction_access_branch_normal_heap_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
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
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heapPointer.toNat)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeHeap : watchedArray.toNat + watchedCount.toNat * 16 ≤ heapPointer.toNat)
    (beforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (headerFits : tx.toNat + 216 < 2^64)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (budget : txListItemAccessCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAccessBranch = (none,final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  rw [source_transaction_access_branch,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      have equal := (Prod.mk.inj run).2
      subst final
      exact watchedValid
    · exact transaction_access_extraction_normal_heap_outer_prefix state final array count index tx input inputLength scratch frame heapPointer ceiling inputLimit
        arrayLocal indexLocal txLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
        heap heapBound countLimit heapArena inputBeforeHeap inputBeforeFrame heapAbove arrayAbove arrayBeforeHeap watchedArray watchedCount watchedInput watchedLength watchedValid watchedAbove watchedBeforeHeap beforeTx headerFits heapAligned budget run
  · cases run

#print axioms transaction_access_branch_normal_heap_outer_prefix
end InitECandidate.Runtime
