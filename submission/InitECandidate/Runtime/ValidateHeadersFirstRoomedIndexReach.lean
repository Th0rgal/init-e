import InitECandidate.Runtime.ValidateHeadersStoredRootsInitial
import InitECandidate.Runtime.ValidateHeadersFirstPointerInvariant
import InitECandidate.Runtime.ValidateHeadersFirstIndexReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual index initialization starts with an empty initialized pointer
prefix. The buffer frontier premise is supplied by the two real allocations. -/
theorem validate_headers_first_roomed_index_reaches {F : Type}
    (e : ValidateHeadersFirstEnvironment) (s : PanSemStateFiniteExact 64 F)
    (ready : ValidateHeadersFirstReady e s)
    (heap : BitVec 64)
    (binding : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (bufferFrontier : e.hs.toNat+e.count.toNat*8≤heap.toNat)
    (hashFloor : e.hashes.toNat+e.count.toNat*32+32≤heap.toNat)
    (heapUpper : heap.toNat≤33805929128) :
    Reaches s (validateHeadersAt 3)
      (fun post => ValidateHeadersStoredRootsRoomedInvariant e post e.count.toNat ∧ post.code = s.code)
      0 (validateHeadersAt 4) := by
  rw [source_validate_headers_index_init]
  apply reaches_dec
  intro value initialized
  have same : value = .val (.word (0 : BitVec 64)) := by simpa [evalHOLExact] using initialized.symm
  subst value
  let post := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) s
  have pointer : ValidateHeadersFirstPointerInvariant e post e.count.toNat := by
    refine ⟨validate_headers_first_index_invariant e s ready,?_,⟨heap,binding,bufferFrontier⟩⟩
    refine ⟨0,?_,?_⟩
    · simp [post,setVarHOLFinite,FUPDATE]
    · exact headerPointerPrefix_empty _ _
  exact ⟨0,rfl,validate_headers_stored_roots_roomed_initial e post heap pointer binding hashFloor heapUpper,rfl⟩

#print axioms validate_headers_first_roomed_index_reaches
end InitECandidate.Runtime
