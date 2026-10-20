import InitECandidate.Runtime.TrieNodeKinds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual fresh leaf constructor preserves every old exact tag and
installs its own real source tag at the newly allocated record. -/
theorem NodeNewLeafDeclarationReady.node_kinds {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length valuePointer valueLength : BitVec 64} {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches) :
 TrieNodeKinds post (insert pointer live) extensions branches := by
 have frame (node : BitVec 64) (member : node∈live) : post.memory node=s.memory node := by
  apply ready.memory
  have positive:=world.layout.positive node member
  have allocated:=world.allocated node member
  omega
 constructor
 · intro node member noExtension noBranch
   rcases member with fresh|old
   · subst node;exact ready.kind
   · rw [frame node old];exact kinds.leaf node old noExtension noBranch
 · intro node member
   rw [frame node (world.layout.extensionLive member)];exact kinds.extension node member
 · intro node member
   rw [frame node (world.layout.branchLive member)];exact kinds.branch node member

#print axioms NodeNewLeafDeclarationReady.node_kinds

/-- The actual fresh ext constructor preserves every old exact tag and
installs its own real source tag at the newly allocated record. -/
theorem NodeNewExtDeclarationReady.node_kinds {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child : BitVec 64} {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches) :
 TrieNodeKinds post (insert pointer live) (insert pointer extensions) branches := by
 have frame (node : BitVec 64) (member : node∈live) : post.memory node=s.memory node := by
  apply ready.memory
  have positive:=world.layout.positive node member
  have allocated:=world.allocated node member
  omega
 constructor
 · intro node member noExtension noBranch
   rcases member with fresh|old
   · subst node;exact False.elim (noExtension (Or.inl rfl))
   · rw [frame node old]
     exact kinds.leaf node old (fun member=>noExtension (Or.inr member)) noBranch
 · intro node member
   rcases member with fresh|old
   · subst node;exact ready.kind
   · rw [frame node (world.layout.extensionLive old)];exact kinds.extension node old
 · intro node member
   rw [frame node (world.layout.branchLive member)];exact kinds.branch node member

#print axioms NodeNewExtDeclarationReady.node_kinds

/-- The actual fresh branch constructor preserves every old exact tag and
installs its own real source tag at the newly allocated record. -/
theorem NodeNewBranchDeclarationReady.node_kinds {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer : BitVec 64} {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches) :
 TrieNodeKinds post (insert pointer live) extensions (insert pointer branches) := by
 have frame (node : BitVec 64) (member : node∈live) : post.memory node=s.memory node := by
  apply ready.memory
  have positive:=world.layout.positive node member
  have allocated:=world.allocated node member
  omega
 constructor
 · intro node member noExtension noBranch
   rcases member with fresh|old
   · subst node;exact False.elim (noBranch (Or.inl rfl))
   · rw [frame node old]
     exact kinds.leaf node old noExtension (fun member=>noBranch (Or.inr member))
 · intro node member
   rw [frame node (world.layout.extensionLive member)];exact kinds.extension node member
 · intro node member
   rcases member with fresh|old
   · subst node;exact ready.kind
   · rw [frame node (world.layout.branchLive old)];exact kinds.branch node old

#print axioms NodeNewBranchDeclarationReady.node_kinds

end InitECandidate.Runtime
