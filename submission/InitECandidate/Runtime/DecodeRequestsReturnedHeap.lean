import InitECandidate.Runtime.DecodeRequestsReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful request decoder allocates its 80-byte header within the
real heap cap and preserves every other global. -/
theorem decodeRequests_returned_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length heapPointer offsets : BitVec 64) (value : ValueHOL 64)
    (heapBound : heapPointer.toNat ≤ 33806089496)
    (returned : DecodeRequestsReturned state pointer length heapPointer offsets value post) :
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧
      ∀ key, key ≠ ofString "heap_ptr" → post.globals.lookup key = state.globals.lookup key := by
  obtain ⟨_,memory,_,_,facts⟩ := returned
  dsimp only [ReqArrayFacts] at facts
  obtain ⟨request,_,_,_,_,_,_,_,_,_,_,_,_,_,globals,_⟩ := facts
  refine ⟨allocationEnd heapPointer 80,?_,allocationEnd_within_heap heapPointer 80 heapBound request,?_⟩
  · rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key different
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms decodeRequests_returned_heap
end InitECandidate.Runtime
