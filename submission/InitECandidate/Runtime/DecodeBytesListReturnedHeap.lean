import InitECandidate.Runtime.DecodeBytesListBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful list splitting preserves the real heap cap and every global
other than the allocator pointer; no alignment or future reserve is assumed. -/
theorem sszSplitReturned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length limit heapPointer : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496)
    (returned : SszSplitVarListReturned state length limit heapPointer value post) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧
      ∀ key, key ≠ ofString "heap_ptr" → post.globals.lookup key = state.globals.lookup key := by
  rcases returned with ⟨_,_,globals⟩ | ⟨_,first,_,_,_,_,request,globals⟩
  · refine ⟨heapPointer,?_,heapBound,?_⟩
    · rw [globals]; exact heap
    · intro key different; rw [globals]
  · refine ⟨allocationEnd heapPointer ((first >>> (2 : Nat)) * 16),?_,
      allocationEnd_within_heap heapPointer _ heapBound request,?_⟩
    · rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · intro key different
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

/-- Byte-list item validation retains the split decoder's heap/global frame. -/
theorem decodeBytesList_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length limit maxBytes heapPointer : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496)
    (returned : DecodeBytesListReturned state pointer length limit maxBytes heapPointer value post) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧
      ∀ key, key ≠ ofString "heap_ptr" → post.globals.lookup key = state.globals.lookup key := by
  obtain ⟨clock,bodyPost,_,body,_,_,globals,_,_⟩ := returned
  let entry : PanSemStateFiniteExact 64 F :=
    {callEntryStateHOLFinite state (bytesListSplitLocals pointer length limit) with clock := clock}
  obtain ⟨nextHeap,nextGlobal,nextBound,other⟩ := sszSplitReturned_heap entry bodyPost length limit heapPointer value heap heapBound body
  refine ⟨nextHeap,?_,nextBound,?_⟩
  · rw [globals]; exact nextGlobal
  · intro key different
    rw [globals]
    exact other key different

#print axioms sszSplitReturned_heap
#print axioms decodeBytesList_returned_heap
end InitECandidate.Runtime
