import InitECandidate.Runtime.TrieWalkRegistryAllocationFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

theorem trieWalkRegistry_empty {F : Type} (state : PanSemStateFiniteExact 64 F) :
    TrieWalkRegistry ∅ ∅ ∅ state := by
  refine ⟨extensionOrderFamily_empty state,extensionChildrenIn_empty ∅ state,
    branchChildrenIn_empty ∅ state,?_,?_⟩
  · intro node member; cases member
  · intro node member; cases member

#print axioms trieWalkRegistry_empty

/-- Register a fully initialized extension, retaining old edges and classifying
its new kind without imposing branch ordering on its memory fields. -/
theorem TrieWalkRegistry.insert_extension {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (pointer child : BitVec 64)
    (registry : TrieWalkRegistry live extensions branches state)
    (kind : state.memory pointer = .word 2)
    (order : ExtensionRecordOrder state pointer)
    (childField : state.memory (pointer + 48) = .word child)
    (childValid : child = 0 ∨ child ∈ live) :
    TrieWalkRegistry (insert pointer live) (insert pointer extensions) branches state := by
  constructor
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact order
    · exact registry.order node old
  · intro node member next loaded
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node
      have sameChild : child = next := HolWordLab.word.inj (childField.symm.trans loaded)
      subst next
      exact childValid.imp_right (Set.mem_insert_of_mem pointer)
    · exact (registry.extensionChildren node old next loaded).imp_right (Set.mem_insert_of_mem pointer)
  · exact registry.branchChildren.mono (Set.subset_insert pointer live)
  · intro node member loaded
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (registry.extensionKind node old loaded)
  · intro node member value loaded nonzero nonleaf nonext
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node
      have equal : (2 : BitVec 64) = value := HolWordLab.word.inj (kind.symm.trans loaded)
      exact False.elim (nonext equal.symm)
    · exact registry.branchKind node old value loaded nonzero nonleaf nonext

#print axioms TrieWalkRegistry.insert_extension
end InitECandidate.Runtime
