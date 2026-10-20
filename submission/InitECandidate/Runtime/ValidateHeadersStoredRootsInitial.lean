import InitECandidate.Runtime.ValidateHeadersStoredRootsRoomedStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual zero-index pointer invariant starts the stored-root invariant
with an empty prefix. A concrete caller heap bound supplies all ranked room. -/
theorem validate_headers_stored_roots_roomed_initial {F : Type}
    (e : ValidateHeadersFirstEnvironment) (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64)
    (valid : ValidateHeadersFirstPointerInvariant e state e.count.toNat)
    (binding : state.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (floor : e.hashes.toNat+e.count.toNat*32+32≤heap.toNat)
    (upper : heap.toNat≤33805929128) :
    ValidateHeadersStoredRootsRoomedInvariant e state e.count.toNat := by
  obtain ⟨index,runtimeHeap,arr,count,atIndex,hs,hashes,within,distance,rest⟩ := valid.1
  have indexZero : index=0 := by
    apply BitVec.eq_of_toNat_eq
    change index.toNat=0
    omega
  refine ⟨⟨valid,⟨0,heap,?_,binding,floor,?_⟩⟩,?_⟩
  · simpa only [indexZero] using atIndex
  · exact validateHeadersStoredRoots_empty state e.hs heap.toNat _
  · intro actual actualBinding
    have same : actual=heap := by
      simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actualBinding.symm.trans binding
    subst actual
    have cap := e.cap
    change heap.toNat+(e.count.toNat+1)*624≤33806089496
    omega

#print axioms validate_headers_stored_roots_roomed_initial
end InitECandidate.Runtime
