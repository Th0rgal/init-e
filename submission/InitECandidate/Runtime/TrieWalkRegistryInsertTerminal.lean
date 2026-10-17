import InitECandidate.Runtime.TrieWalkRegistry
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Leaf and unresolved-hash nodes terminate traversal. Registering such a
node enlarges the live set without adding extension or branch obligations. -/
theorem TrieWalkRegistry.insert_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (live extensions branches : Set (BitVec 64)) (pointer kind : BitVec 64)
    (registry : TrieWalkRegistry live extensions branches state)
    (kindField : state.memory pointer = .word kind) (terminal : kind = 0 ∨ kind = 1) :
    TrieWalkRegistry (insert pointer live) extensions branches state := by
  constructor
  · exact registry.order
  · exact registry.extensionChildren.mono (Set.subset_insert pointer live)
  · exact registry.branchChildren.mono (Set.subset_insert pointer live)
  · intro node member loaded
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node
      have equal : kind = (2 : BitVec 64) := HolWordLab.word.inj (kindField.symm.trans loaded)
      rcases terminal with zero | one <;> simp_all
    · exact registry.extensionKind node old loaded
  · intro node member value loaded nonzero nonleaf nonext
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node
      have equal : kind = value := HolWordLab.word.inj (kindField.symm.trans loaded)
      subst value
      rcases terminal with zero | one
      · exact False.elim (nonzero zero)
      · exact False.elim (nonleaf one)
    · exact registry.branchKind node old value loaded nonzero nonleaf nonext

#print axioms TrieWalkRegistry.insert_terminal
end InitECandidate.Runtime
