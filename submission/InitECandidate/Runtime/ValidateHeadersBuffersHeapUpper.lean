import InitECandidate.Runtime.ValidateHeadersBuffers
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual successful header-buffer allocations add at most forty bytes per
header and fifty-six fixed bytes, including alignment padding. -/
theorem validate_headers_buffers_heap_upper {F : Type}
    (state first post : PanSemStateFiniteExact 64 F) (count heap : BitVec 64)
    (small : count.toNat≤256)
    (hsAllocation : AllocationDeclarationReady state (ofString "hs") heap (validateHeadersHsSize count) first)
    (hashAllocation : AllocationDeclarationReady first (ofString "hashes")
      (allocationEnd heap (validateHeadersHsSize count)) (validateHeadersHashesSize count) post) :
    let hashes := allocationEnd heap (validateHeadersHsSize count)
    let finalHeap := allocationEnd hashes (validateHeadersHashesSize count)
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
      hashes.toNat+count.toNat*32+32≤finalHeap.toNat ∧
      finalHeap.toNat≤heap.toNat+count.toNat*40+56 ∧
      (heap.toNat≤33805910000→finalHeap.toNat≤33805929128) := by
  dsimp only
  obtain ⟨hsSize,hashSize⟩ := validate_headers_allocation_sizes count small
  obtain ⟨_,_,_,_,_,firstCap,firstExtent,_⟩ := hsAllocation
  obtain ⟨_,_,_,_,globals,finalCap,finalExtent,_⟩ := hashAllocation
  have firstFits : heap.toNat+(validateHeadersHsSize count).toNat≤33806089496 := by omega
  have finalFits : (allocationEnd heap (validateHeadersHsSize count)).toNat+
      (validateHeadersHashesSize count).toNat≤33806089496 := by omega
  have firstUpper := (allocationEnd_covers heap (validateHeadersHsSize count) firstFits).2.1
  have finalUpper := (allocationEnd_covers (allocationEnd heap (validateHeadersHsSize count))
    (validateHeadersHashesSize count) finalFits).2.1
  rw [hsSize] at firstUpper
  rw [hashSize] at finalUpper finalExtent
  refine ⟨?_,finalExtent,by omega,?_⟩
  · rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro upper
    omega

#print axioms validate_headers_buffers_heap_upper
end InitECandidate.Runtime
