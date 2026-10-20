import InitECandidate.Runtime.TrieLeafAllocationFloor
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Actual fresh extension allocation preserves record and stored-key lower bounds. -/
theorem NodeNewExtDeclarationReady.allocation_floor {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child : BitVec 64} {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64→Nat} {floor : Nat}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤pointer.toNat) (keyAbove : floor≤nib.toNat) :
 TrieAllocationFloor post (insert pointer live) branches floor := by
 have headerFrame (node : BitVec 64) (member : node∈live) (nonBranch : node∉branches)
  (offset : Nat) (small : offset<48) :
  post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  apply ready.memory
  have capacity:=paths.header_capacity world.layout node member nonBranch
  rw [world.layout.field_nat node member offset (by omega)]
  have:=world.allocated node member
  omega
 constructor
 · intro node member
   rcases member with fresh|old
   · subst node;exact heapAbove
   · exact lower.records node old
 · intro node member nonBranch key len keyAt lenAt
   rcases member with fresh|old
   · subst node
     have same : nib=key:=HolWordLab.word.inj (ready.nibAt.symm.trans keyAt)
     rw [←same];exact keyAbove
   · apply lower.keys node old nonBranch key len
     · exact (headerFrame node old nonBranch 32 (by decide)).symm.trans keyAt
     · exact (headerFrame node old nonBranch 40 (by decide)).symm.trans lenAt


#print axioms NodeNewExtDeclarationReady.allocation_floor

/-- Actual branch allocation adds no stored path and preserves all old key floors. -/
theorem NodeNewBranchDeclarationReady.allocation_floor {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer : BitVec 64} {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64→Nat} {floor : Nat}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (lower : TrieAllocationFloor s live branches floor)
 (heapAbove : floor≤pointer.toNat) :
 TrieAllocationFloor post (insert pointer live) (insert pointer branches) floor := by
 have headerFrame (node : BitVec 64) (member : node∈live) (nonBranch : node∉branches)
  (offset : Nat) (small : offset<48) :
  post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  apply ready.memory
  have capacity:=paths.header_capacity world.layout node member nonBranch
  rw [world.layout.field_nat node member offset (by omega)]
  have:=world.allocated node member
  omega
 constructor
 · intro node member
   rcases member with fresh|old
   · subst node;exact heapAbove
   · exact lower.records node old
 · intro node member nonBranch key len keyAt lenAt
   rcases member with fresh|old
   · subst node
     exact False.elim (nonBranch (Or.inl rfl))
   · have oldNonBranch : node∉branches:=fun member=>nonBranch (Or.inr member)
     apply lower.keys node old oldNonBranch key len
     · exact (headerFrame node old oldNonBranch 32 (by decide)).symm.trans keyAt
     · exact (headerFrame node old oldNonBranch 40 (by decide)).symm.trans lenAt


#print axioms NodeNewBranchDeclarationReady.allocation_floor
end InitECandidate.Runtime
