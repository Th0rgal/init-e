import InitECandidate.Runtime.TransactionAuthorizationBranchOuterPrefix
import InitECandidate.Runtime.TransactionAuthorizationExtractionHeapOuterPrefix
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxListItemHeapInputPrefix
import InitECandidate.Runtime.TxListItemHeapIndependentOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Executing or skipping the actual authorization conditional retains transaction slices. -/
theorem transaction_authorization_branch_normal_heap_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
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
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heapPointer.toNat)
    (headerBefore : tx.toNat + 280 < array.toNat)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64) (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeHeap : watchedArray.toNat + watchedCount.toNat * 16 ≤ heapPointer.toNat)
    (watchedBeforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (budget : txListItemAuthorizationCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAuthorizationBranch = (none,final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  rw [source_transaction_authorization_branch,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      have equal := (Prod.mk.inj run).2
      subst final
      exact watchedValid
    · exact transaction_authorization_extraction_normal_heap_outer_prefix state final array count index tx input inputLength scratch frame heapPointer ceiling inputLimit
        arrayLocal indexLocal txLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
        heap heapBound countLimit heapArena inputBeforeHeap inputBeforeFrame heapAbove arrayFits arrayAbove arrayBeforeHeap headerBefore watchedArray watchedCount watchedInput watchedLength watchedValid watchedFits watchedAbove watchedBeforeHeap watchedBeforeTx heapAligned budget run
  · cases run

#print axioms transaction_authorization_branch_normal_heap_outer_prefix
end InitECandidate.Runtime
