import InitECandidate.Runtime.TransactionAccessExtractionGuardedHeapGrowth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete access conditional retains cumulative heap and scratch/frame guarantees. -/
theorem transaction_access_branch_normal_guarded_heap_growth {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count index input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
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
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (budget : txListItemAccessCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAccessBranch = (none,final)) :
    ∃ nextHeap : BitVec 64,
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ heapPointer.toNat + inputLength.toNat * 40 + (inputLength.toNat * 48 + 46) * inputLength.toNat ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  rw [source_transaction_access_branch,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      have equal := (Prod.mk.inj run).2
      subst final
      exact ⟨heapPointer,heap,by omega,heapBound,heapAligned,scratchGlobal,frameGlobal⟩
    · exact transaction_access_extraction_normal_guarded_heap_growth state final array count index input inputLength scratch frame heapPointer ceiling inputLimit
        arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
        heap heapBound countLimit heapArena inputBeforeHeap inputBeforeFrame heapAbove heapAligned budget run
  · cases run

#print axioms transaction_access_branch_normal_guarded_heap_growth
end InitECandidate.Runtime
