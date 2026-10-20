import InitECandidate.Runtime.TrieNodePaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A returned actual leaf constructor installs its real segment header
and preserves every old node path, including byte-cell separation. -/
theorem NodeNewLeafDeclarationReady.node_paths {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length valuePointer valueLength : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size nib length pointer) (short : length.toNat≤18) :
 TrieNodePaths post (insert pointer live) extensions branches (Function.update size pointer 64) (allocationEnd pointer 64) := by
 classical
 have oldDifferent (node : BitVec 64) (member : node∈live) : node≠pointer := by
  intro same;subst node
  have:=world.layout.positive pointer member
  have:=world.allocated pointer member
  omega
 have headerFrame (node : BitVec 64) (member : node∈live) (nonBranch : node∉branches)
  (offset : Nat) (inside : offset<48) : post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  apply ready.memory
  have capacity:=paths.header_capacity world.layout node member nonBranch
  rw [world.layout.field_nat node member offset (by omega)]
  have:=world.allocated node member
  omega
 constructor
 · intro node member nonExt nonBranch
   rcases member with fresh|old
   · subst node;simp
   · simpa [Function.update_of_ne (oldDifferent node old)] using paths.leafCapacity node old nonExt nonBranch
 · intro node member nonBranch
   rcases member with fresh|old
   · subst node
     exact ⟨nib,length,ready.nibAt,ready.lengthAt,short,ready.path_buffer world keyPath⟩
   · obtain ⟨key,len,keyAt,lenAt,small,path⟩:=paths.paths node old nonBranch
     refine ⟨key,len,?_,?_,small,ready.path_buffer world path⟩
     · rw [show node+32=node+BitVec.ofNat 64 32 from rfl,headerFrame node old nonBranch 32 (by decide)];exact keyAt
     · rw [show node+40=node+BitVec.ofNat 64 40 from rfl,headerFrame node old nonBranch 40 (by decide)];exact lenAt

#print axioms NodeNewLeafDeclarationReady.node_paths

/-- A returned actual extension constructor installs its real segment header
and preserves every old node path, including byte-cell separation. -/
theorem NodeNewExtDeclarationReady.node_paths {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size nib length pointer) (short : length.toNat≤18) :
 TrieNodePaths post (insert pointer live) (insert pointer extensions) branches (Function.update size pointer 56) (allocationEnd pointer 56) := by
 classical
 have oldDifferent (node : BitVec 64) (member : node∈live) : node≠pointer := by
  intro same;subst node
  have:=world.layout.positive pointer member
  have:=world.allocated pointer member
  omega
 have headerFrame (node : BitVec 64) (member : node∈live) (nonBranch : node∉branches)
  (offset : Nat) (inside : offset<48) : post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  apply ready.memory
  have capacity:=paths.header_capacity world.layout node member nonBranch
  rw [world.layout.field_nat node member offset (by omega)]
  have:=world.allocated node member
  omega
 constructor
 · intro node member nonExt nonBranch
   rcases member with fresh|old
   · subst node;exact False.elim (nonExt (Or.inl rfl))
   · simpa [Function.update_of_ne (oldDifferent node old)] using paths.leafCapacity node old (fun member=>nonExt (Or.inr member)) nonBranch
 · intro node member nonBranch
   rcases member with fresh|old
   · subst node
     exact ⟨nib,length,ready.nibAt,ready.lengthAt,short,ready.path_buffer world keyPath⟩
   · obtain ⟨key,len,keyAt,lenAt,small,path⟩:=paths.paths node old nonBranch
     refine ⟨key,len,?_,?_,small,ready.path_buffer world path⟩
     · rw [show node+32=node+BitVec.ofNat 64 32 from rfl,headerFrame node old nonBranch 32 (by decide)];exact keyAt
     · rw [show node+40=node+BitVec.ofNat 64 40 from rfl,headerFrame node old nonBranch 40 (by decide)];exact lenAt

#print axioms NodeNewExtDeclarationReady.node_paths

/-- A returned actual branch constructor adds no segment header, while
all existing leaf/extension paths survive its fresh record initialization. -/
theorem NodeNewBranchDeclarationReady.node_paths {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS} {pointer : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer) :
 TrieNodePaths post (insert pointer live) extensions (insert pointer branches) (Function.update size pointer 176) (allocationEnd pointer 176) := by
 classical
 have oldDifferent (node : BitVec 64) (member : node∈live) : node≠pointer := by
  intro same;subst node
  have:=world.layout.positive pointer member
  have:=world.allocated pointer member
  omega
 have headerFrame (node : BitVec 64) (member : node∈live) (nonBranch : node∉branches)
  (offset : Nat) (inside : offset<48) : post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  apply ready.memory
  have capacity:=paths.header_capacity world.layout node member nonBranch
  rw [world.layout.field_nat node member offset (by omega)]
  have:=world.allocated node member
  omega
 constructor
 · intro node member nonExt nonBranch
   rcases member with fresh|old
   · subst node;exact False.elim (nonBranch (Or.inl rfl))
   · simpa [Function.update_of_ne (oldDifferent node old)] using paths.leafCapacity node old nonExt (fun member=>nonBranch (Or.inr member))
 · intro node member nonBranch
   rcases member with fresh|old
   · subst node;exact False.elim (nonBranch (Or.inl rfl))
   · have oldNonBranch : node∉branches:=fun member=>nonBranch (Or.inr member)
     obtain ⟨key,len,keyAt,lenAt,small,path⟩:=paths.paths node old oldNonBranch
     refine ⟨key,len,?_,?_,small,ready.path_buffer world path⟩
     · rw [show node+32=node+BitVec.ofNat 64 32 from rfl,headerFrame node old oldNonBranch 32 (by decide)];exact keyAt
     · rw [show node+40=node+BitVec.ofNat 64 40 from rfl,headerFrame node old oldNonBranch 40 (by decide)];exact lenAt

#print axioms NodeNewBranchDeclarationReady.node_paths

end InitECandidate.Runtime
