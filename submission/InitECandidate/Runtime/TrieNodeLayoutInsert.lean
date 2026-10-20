import InitECandidate.Runtime.TrieNodeLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A fresh actual allocation extends the disjoint record layout. The old
record endpoints, rather than merely observed words, lie below its pointer. -/
theorem TrieNodeLayout.insert_record {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
 (pointer : BitVec 64) (bytes : Nat) (positive : 0<bytes)
 (below : ∀node∈live,node.toNat+size node≤pointer.toNat)
 (bounded : pointer.toNat+bytes≤2^64) :
 TrieNodeLayout (insert pointer live) extensions branches (Function.update size pointer bytes) := by
 classical
 have fresh : pointer∉live := by
  intro member
  have := below pointer member
  have := layout.positive pointer member
  omega
 have kept : ∀node∈live,Function.update size pointer bytes node=size node := by
  intro node member
  have different : node≠pointer := by
   intro same
   subst node
   exact fresh member
  simp [Function.update,different]
 constructor
 · intro node member
   rcases member with same|old
   · subst node;simpa using positive
   · rw [kept node old];exact layout.positive node old
 · intro node member
   rcases member with same|old
   · subst node;simpa using bounded
   · rw [kept node old];exact layout.bounded node old
 · intro node member other otherMember different
   rcases member with same|old
   · subst node
     rcases otherMember with same|otherOld
     · exact False.elim (different same.symm)
     · exact Or.inr (by rw [kept other otherOld];exact below other otherOld)
   · rcases otherMember with same|otherOld
     · subst other
       exact Or.inl (by rw [kept node old];exact below node old)
     · rw [kept node old,kept other otherOld]
       exact layout.separate node old other otherOld different
 · intro node member
   exact Or.inr (layout.extensionLive member)
 · intro node member
   exact Or.inr (layout.branchLive member)
 · intro node member
   rw [kept node (layout.extensionLive member)]
   exact layout.extensionSize node member
 · intro node member
   rw [kept node (layout.branchLive member)]
   exact layout.branchSize node member
 · exact layout.differentKinds

theorem TrieNodeLayout.insert_extension {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
 (pointer : BitVec 64) (bytes : Nat) (capacity : 56≤bytes)
 (below : ∀node∈live,node.toNat+size node≤pointer.toNat)
 (bounded : pointer.toNat+bytes≤2^64) :
 TrieNodeLayout (insert pointer live) (insert pointer extensions) branches (Function.update size pointer bytes) := by
 classical
 have base:=layout.insert_record pointer bytes (by omega) below bounded
 have fresh : pointer∉live := by
  intro member
  have := below pointer member
  have := layout.positive pointer member
  omega
 refine ⟨base.positive,base.bounded,base.separate,?_,base.branchLive,?_,base.branchSize,?_⟩
 · intro node member
   rcases member with same|old
   · exact Or.inl same
   · exact Or.inr (layout.extensionLive old)
 · intro node member
   rcases member with same|old
   · subst node;simpa using capacity
   · exact base.extensionSize node old
 · apply Set.disjoint_left.mpr
   intro node member branch
   rcases member with same|old
   · subst node;exact fresh (layout.branchLive branch)
   · exact Set.disjoint_left.mp layout.differentKinds old branch

theorem TrieNodeLayout.insert_branch {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
 (pointer : BitVec 64) (bytes : Nat) (capacity : 176≤bytes)
 (below : ∀node∈live,node.toNat+size node≤pointer.toNat)
 (bounded : pointer.toNat+bytes≤2^64) :
 TrieNodeLayout (insert pointer live) extensions (insert pointer branches) (Function.update size pointer bytes) := by
 classical
 have base:=layout.insert_record pointer bytes (by omega) below bounded
 have fresh : pointer∉live := by
  intro member
  have := below pointer member
  have := layout.positive pointer member
  omega
 refine ⟨base.positive,base.bounded,base.separate,base.extensionLive,?_,base.extensionSize,?_,?_⟩
 · intro node member
   rcases member with same|old
   · exact Or.inl same
   · exact Or.inr (layout.branchLive old)
 · intro node member
   rcases member with same|old
   · subst node;simpa using capacity
   · exact base.branchSize node old
 · apply Set.disjoint_left.mpr
   intro node extension member
   rcases member with same|old
   · subst node;exact fresh (layout.extensionLive extension)
   · exact Set.disjoint_left.mp layout.differentKinds extension old

#print axioms TrieNodeLayout.insert_record
#print axioms TrieNodeLayout.insert_extension
#print axioms TrieNodeLayout.insert_branch
end InitECandidate.Runtime
