import InitECandidate.Runtime.TransactionAuthorizationExtractionHeapGrowth
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_authorization_branch_normal_heap_growth {F : Type} (state final : PanSemStateFiniteExact 64 F)
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
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (heapBeforeFrame : heapPointer.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (reserve : heapPointer.toNat + inputLength.toNat * 248 ≤ frame.toNat)
    (budget : txListItemAuthorizationCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAuthorizationBranch = (none,final)) :
    ∃ nextHeap : BitVec 64,
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      heapPointer.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ heapPointer.toNat + inputLength.toNat * 232 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  rw [source_transaction_authorization_branch,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_skip] at run
      have equal := (Prod.mk.inj run).2
      subst final
      exact ⟨heapPointer,heap,Nat.le_refl _,by omega,heapBound,heapAligned,scratchGlobal,frameGlobal⟩
    · exact transaction_authorization_extraction_normal_heap_growth state final array count index input inputLength scratch frame heapPointer ceiling inputLimit
        arrayLocal indexLocal valid inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap heapBound
        countLimit heapArena inputBeforeHeap heapBeforeFrame heapAligned reserve budget run
  · cases run

#print axioms transaction_authorization_branch_normal_heap_growth
end InitECandidate.Runtime
