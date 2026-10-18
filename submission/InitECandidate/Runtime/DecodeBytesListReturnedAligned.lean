import InitECandidate.Runtime.DecodeBytesListReturnedHeap
import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Capped, aligned heap and non-allocator globals after a returned split. -/
theorem sszSplitReturned_heap_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length limit heapPointer : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (returned : SszSplitVarListReturned state length limit heapPointer value post) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      ∀ key, key ≠ ofString "heap_ptr" → post.globals.lookup key = state.globals.lookup key := by
  rcases returned with ⟨_,_,globals⟩ | ⟨_,first,_,_,_,_,request,globals⟩
  · refine ⟨heapPointer,?_,heapBound,aligned,?_⟩
    · rw [globals]; exact heap
    · intro key different; rw [globals]
  · have sum := allocationGuard_sum_bound heapPointer _ heapBound request
    refine ⟨allocationEnd heapPointer ((first >>> (2 : Nat)) * 16),?_,
      allocationEnd_within_heap heapPointer _ heapBound request, (allocationEnd_covers _ _ sum).2.2, ?_⟩
    · rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro key different
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

theorem decodeBytesList_returned_heap_aligned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length limit maxBytes heapPointer : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (returned : DecodeBytesListReturned state pointer length limit maxBytes heapPointer value post) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      ∀ key, key ≠ ofString "heap_ptr" → post.globals.lookup key = state.globals.lookup key := by
  obtain ⟨clock,bodyPost,_,body,_,_,globals,_,_⟩ := returned
  let entry : PanSemStateFiniteExact 64 F :=
    {callEntryStateHOLFinite state (bytesListSplitLocals pointer length limit) with clock := clock}
  obtain ⟨nextHeap,nextGlobal,nextBound,nextAligned,other⟩ :=
    sszSplitReturned_heap_aligned entry bodyPost length limit heapPointer value heap heapBound aligned body
  refine ⟨nextHeap,?_,nextBound,nextAligned,?_⟩
  · rw [globals]; exact nextGlobal
  · intro key different
    rw [globals]
    exact other key different

#print axioms decodeBytesList_returned_heap_aligned
end InitECandidate.Runtime
