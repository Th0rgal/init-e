import InitECandidate.Runtime.TrieWalkRegistryAllocationFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Register a fully initialized branch with sixteen null children, retaining
old live edges and classifying the new record as a branch. -/
theorem TrieWalkRegistry.insert_branch {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (pointer : BitVec 64)
    (registry : TrieWalkRegistry live extensions branches state)
    (kind : state.memory pointer = .word 3)
    (children : ∀ slot : Nat, slot < 16 → state.memory (branchChildAddress pointer slot) = .word 0) :
    TrieWalkRegistry (insert pointer live) extensions (insert pointer branches) state := by
  constructor
  · exact registry.order
  · exact registry.extensionChildren.mono (Set.subset_insert pointer live)
  · intro node member slot small child loaded
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node
      have zero := children slot small
      exact Or.inl (HolWordLab.word.inj (loaded.symm.trans zero))
    · exact (registry.branchChildren node old slot small child loaded).imp_right (Set.mem_insert_of_mem pointer)
  · intro node member loaded
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node
      have impossible : (3 : BitVec 64) = 2 := HolWordLab.word.inj (kind.symm.trans loaded)
      contradiction
    · exact registry.extensionKind node old loaded
  · intro node member value loaded nonzero nonleaf nonext
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (registry.branchKind node old value loaded nonzero nonleaf nonext)

#print axioms TrieWalkRegistry.insert_branch
end InitECandidate.Runtime
