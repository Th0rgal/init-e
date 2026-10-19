import InitECandidate.Runtime.ValidateHeadersAllocationReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The two real allocation outcomes give separated, bounded header-pointer
and hash buffers while retaining the original witness memory and count. -/
theorem validate_headers_buffers {F : Type} (s first post : PanSemStateFiniteExact 64 F) (n heap : BitVec 64)
    (small : n.toNat ≤ 256)
    (atCount : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hsAllocation : AllocationDeclarationReady s (ofString "hs") heap (validateHeadersHsSize n) first)
    (hashAllocation : AllocationDeclarationReady first (ofString "hashes") (allocationEnd heap (validateHeadersHsSize n))
      (validateHeadersHashesSize n) post) :
    let hashHeap := allocationEnd heap (validateHeadersHsSize n)
    let finalHeap := allocationEnd hashHeap (validateHeadersHashesSize n)
    post.locals.lookup (ofString "hs") = some (.val (.word heap)) ∧
    post.locals.lookup (ofString "hashes") = some (.val (.word hashHeap)) ∧
    post.locals.lookup (ofString "n") = some (.val (.word n)) ∧
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
    post.memory = s.memory ∧ post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
    heap.toNat + n.toNat * 8 + 8 ≤ hashHeap.toNat ∧
    hashHeap.toNat + n.toNat * 32 + 32 ≤ finalHeap.toNat ∧
    hashHeap.toNat % 8 = 0 ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
    (∀ name : MlS, name ≠ ofString "heap_ptr" → post.globals.lookup name = s.globals.lookup name) := by
  dsimp only
  obtain ⟨firstLocals,firstMemory,firstCode,firstDomain,firstGlobals,_,firstExtent,firstAlign⟩ := hsAllocation
  obtain ⟨postLocals,postMemory,postCode,postDomain,postGlobals,postCap,postExtent,postAlign⟩ := hashAllocation
  obtain ⟨hsSize,hashSize⟩ := validate_headers_allocation_sizes n small
  refine ⟨?_,?_,?_,?_,postMemory.trans firstMemory,postDomain.trans firstDomain,postCode.trans firstCode,
    (by rw [hsSize] at firstExtent; omega),(by rw [hashSize] at postExtent; omega),firstAlign,postAlign,postCap,?_⟩
  · rw [postLocals,firstLocals]
    simp (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [postLocals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [postLocals,firstLocals]
    simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atCount
  · rw [postGlobals]; simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro name different
    rw [postGlobals]
    simp only [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,if_neg (Ne.symm different)]
    rw [firstGlobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]

#print axioms validate_headers_buffers
end InitECandidate.Runtime
