import InitECandidate.Runtime.TrieNodeLayout
namespace InitECandidate.Runtime
open Flapjack

def trieRecordSizeInsert (size : BitVec 64 → Nat) (pointer : BitVec 64) (bytes : Nat) : BitVec 64 → Nat :=
  fun node => if node = pointer then bytes else size node

/-- A fresh allocation after every old record extends the disjoint layout.
The size map is updated only at the new pointer. -/
theorem TrieNodeLayout.allocate {live extensions branches : Set (BitVec 64)}
    {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
    (pointer : BitVec 64) (bytes : Nat) (positive : 0 < bytes)
    (bounded : pointer.toNat + bytes ≤ 2^64)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ pointer.toNat) :
    TrieNodeLayout (insert pointer live) extensions branches (trieRecordSizeInsert size pointer bytes) := by
  have fresh : pointer ∉ live := by
    intro member
    have occupied := layout.positive pointer member
    have before := frontier pointer member
    omega
  have different : ∀ node ∈ live, node ≠ pointer := by intro node member same; subst node; exact fresh member
  constructor
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; simpa [trieRecordSizeInsert] using positive
    · simpa [trieRecordSizeInsert,different node old] using layout.positive node old
  · intro node member
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node; simpa [trieRecordSizeInsert] using bounded
    · simpa [trieRecordSizeInsert,different node old] using layout.bounded node old
  · intro node member other otherMember distinct
    rcases Set.mem_insert_iff.mp member with same | old
    · subst node
      have oldOther : other ∈ live := (Set.mem_insert_iff.mp otherMember).resolve_left (Ne.symm distinct)
      right
      simpa [trieRecordSizeInsert,different other oldOther] using frontier other oldOther
    · rcases Set.mem_insert_iff.mp otherMember with same | oldOther
      · subst other
        left
        simpa [trieRecordSizeInsert,different node old] using frontier node old
      · simpa [trieRecordSizeInsert,different node old,different other oldOther] using
          layout.separate node old other oldOther distinct
  · intro node member
    exact Set.mem_insert_of_mem _ (layout.extensionLive member)
  · intro node member
    exact Set.mem_insert_of_mem _ (layout.branchLive member)
  · intro node member
    simpa [trieRecordSizeInsert,different node (layout.extensionLive member)] using layout.extensionSize node member
  · intro node member
    simpa [trieRecordSizeInsert,different node (layout.branchLive member)] using layout.branchSize node member
  · exact layout.differentKinds

/-- A freshly allocated record may be classified as an extension once its
capacity is known; the interval proof remains unchanged. -/
theorem TrieNodeLayout.register_extension {live extensions branches : Set (BitVec 64)}
    {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
    (pointer : BitVec 64) (member : pointer ∈ live) (capacity : 56 ≤ size pointer)
    (notBranch : pointer ∉ branches) :
    TrieNodeLayout live (insert pointer extensions) branches size := by
  refine ⟨layout.positive,layout.bounded,layout.separate,?_,layout.branchLive,?_,layout.branchSize,?_⟩
  · intro node included
    rcases Set.mem_insert_iff.mp included with same | old
    · subst node; exact member
    · exact layout.extensionLive old
  · intro node included
    rcases Set.mem_insert_iff.mp included with same | old
    · subst node; exact capacity
    · exact layout.extensionSize node old
  · apply Set.disjoint_left.mpr
    intro node included branch
    rcases Set.mem_insert_iff.mp included with same | old
    · subst node; exact notBranch branch
    · exact Set.disjoint_left.mp layout.differentKinds old branch

theorem TrieNodeLayout.register_branch {live extensions branches : Set (BitVec 64)}
    {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
    (pointer : BitVec 64) (member : pointer ∈ live) (capacity : 176 ≤ size pointer)
    (notExtension : pointer ∉ extensions) :
    TrieNodeLayout live extensions (insert pointer branches) size := by
  refine ⟨layout.positive,layout.bounded,layout.separate,layout.extensionLive,?_,layout.extensionSize,?_,?_⟩
  · intro node included
    rcases Set.mem_insert_iff.mp included with same | old
    · subst node; exact member
    · exact layout.branchLive old
  · intro node included
    rcases Set.mem_insert_iff.mp included with same | old
    · subst node; exact capacity
    · exact layout.branchSize node old
  · apply Set.disjoint_left.mpr
    intro node extension included
    rcases Set.mem_insert_iff.mp included with same | old
    · subst node; exact notExtension extension
    · exact Set.disjoint_left.mp layout.differentKinds extension old

/-- The updated size map retains a frontier bound for every old/new record. -/
theorem TrieNodeLayout.allocate_frontier {live extensions branches : Set (BitVec 64)}
    {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
    (pointer : BitVec 64) (bytes finish : Nat)
    (frontier : ∀ node ∈ live, node.toNat + size node ≤ pointer.toNat)
    (covers : pointer.toNat + bytes ≤ finish) :
    ∀ node ∈ insert pointer live, node.toNat + trieRecordSizeInsert size pointer bytes node ≤ finish := by
  intro node member
  rcases Set.mem_insert_iff.mp member with same | old
  · subst node
    simpa [trieRecordSizeInsert] using covers
  · have distinct : node ≠ pointer := by
      intro same
      subst node
      have occupied := layout.positive pointer old
      have before := frontier pointer old
      omega
    have before := frontier node old
    simp only [trieRecordSizeInsert,if_neg distinct]
    omega

theorem trieNodeLayout_empty (size : BitVec 64 → Nat) : TrieNodeLayout ∅ ∅ ∅ size := by
  constructor
  · intro node member; cases member
  · intro node member; cases member
  · intro node member; cases member
  · intro node member; cases member
  · intro node member; cases member
  · intro node member; cases member
  · intro node member; cases member
  · apply Set.disjoint_left.mpr
    intro node member
    cases member

#print axioms TrieNodeLayout.allocate_frontier
#print axioms trieNodeLayout_empty
#print axioms TrieNodeLayout.allocate
#print axioms TrieNodeLayout.register_extension
#print axioms TrieNodeLayout.register_branch
end InitECandidate.Runtime
