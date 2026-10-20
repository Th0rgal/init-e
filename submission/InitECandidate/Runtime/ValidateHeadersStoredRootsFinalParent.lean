import InitECandidate.Runtime.ValidateHeadersStoredRootsRoomedLoop
/-!
The actual final parent record: `hs[count-1]`.

At rank `0` the loop's typed index has reached the header count, so the stored-record component of
the invariant covers the whole pointer buffer and the record the loop stored for the last header is
the parent.  Its state root word is readable memory, it sits below the live heap and above the
fixed hash-buffer floor.  No caller `h` and no parent selector is assumed: the record comes from
the loop's own stores.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

/-- At rank `0` the loop's index has reached the header count, so the stored records cover the
whole pointer buffer: the record the loop stored for the last header, `hs[count-1]`, is the
actual final parent, and its state root word is readable memory. -/
theorem validate_headers_stored_roots_parent_exhausted {F : Type}
    (e : ValidateHeadersFirstEnvironment) (s : PanSemStateFiniteExact 64 F)
    (exhausted : ValidateHeadersStoredRootsInvariant e s 0) (countNonzero : e.count ≠ 0) :
    ∃ heap header word : BitVec 64,
      s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
      s.memory (e.hs + (e.count - 1) * 8) = .word header ∧
      s.memory (header + 32#64) = .word word ∧
      s.memaddrs (header + 32#64) ∧ header.toNat + 248 ≤ heap.toNat ∧
      e.hashes.toNat + e.count.toNat * 32 + 32 ≤ header.toNat := by
  obtain ⟨valid,⟨index,heap,atIndex,heapGlobal,storedFloor,roots⟩⟩ := exhausted
  obtain ⟨runtime,⟨prefixIndex,atPrefixIndex,initialized⟩,_frontier⟩ := valid
  have sameIndex : prefixIndex = index :=
    HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (atPrefixIndex.symm.trans atIndex)))
  subst prefixIndex
  obtain ⟨runtimeIndex,runtimeHeap,atArray,atCount,atRuntimeIndex,atHs,atHashes,within,distance,rest⟩ :=
    runtime
  have runtimeEq : runtimeIndex = index := by
    exact HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (atRuntimeIndex.symm.trans atIndex)))
  subst runtimeEq
  have sameCount : runtimeIndex.toNat = e.count.toNat := by
    have low := within
    have high := distance
    omega
  have allStored : ValidateHeadersStoredRoots s e.hs e.count.toNat heap.toNat
      (e.hashes.toNat + e.count.toNat * 32 + 32) := by
    exact sameCount ▸ roots
  obtain ⟨header,word,cell,rootWord,rootDomain,extent,aboveFloor⟩ :=
    ValidateHeadersStoredRoots.last s e.hs e.count heap.toNat
      (e.hashes.toNat + e.count.toNat * 32 + 32) allStored countNonzero
  exact ⟨heap,header,word,heapGlobal,cell,rootWord,rootDomain,extent,aboveFloor⟩


#print axioms validate_headers_stored_roots_parent_exhausted
end InitECandidate.Runtime
