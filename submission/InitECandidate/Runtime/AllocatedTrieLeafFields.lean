import InitECandidate.Runtime.TrieNodeKinds
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A real leaf's key/value fields cannot alias any registered traversal word.
Exact tags exclude the same record from extension/branch classifications;
allocated interval separation handles every other record. -/
theorem TrieNodeLayout.leaf_field_not_owned {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (layout : TrieNodeLayout live extensions branches size) (kinds : TrieNodeKinds s live extensions branches)
 (parent : BitVec 64) (member : parent∈live) (capacity : 64≤size parent)
 (tag : s.memory parent=.word (1#64)) (offset : Nat) (lower : 32≤offset) (upper : offset<64) :
 ¬TrieWalkRegistryWord live extensions branches (parent+BitVec.ofNat 64 offset) := by
 obtain ⟨notExtension,notBranch⟩:=kinds.leaf_separate parent tag
 rintro (⟨node,registered,equal⟩|⟨node,registered,atLength|atChild⟩|⟨node,registered,index,inside,equal⟩)
 · have different:=layout.fields_ne parent node member registered offset 0 (by omega) (layout.positive node registered) (Or.inr (by omega))
   exact different (by simpa using equal)
 · have nodes : parent≠node:=by intro same;subst node;exact notExtension registered
   exact layout.fields_separate parent node member (layout.extensionLive registered) nodes offset 40
    (by omega) (by have:=layout.extensionSize node registered;omega) atLength
 · have nodes : parent≠node:=by intro same;subst node;exact notExtension registered
   exact layout.fields_separate parent node member (layout.extensionLive registered) nodes offset 48
    (by omega) (by have:=layout.extensionSize node registered;omega) atChild
 · have nodes : parent≠node:=by intro same;subst node;exact notBranch registered
   have address : branchChildAddress node index=node+BitVec.ofNat 64 (32+index*8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
   rw [address] at equal
   exact layout.fields_separate parent node member (layout.branchLive registered) nodes offset (32+index*8)
    (by omega) (by have:=layout.branchSize node registered;omega) equal

/-- Any actual leaf key/value word store keeps the full allocated traversal
world and exact kind tags. These are the terminal leaf-update fields that the
one-way registry alone could not classify safely. -/
theorem AllocatedTrieWorld.write_leaf_field {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier) (kinds : TrieNodeKinds s live extensions branches)
 (parent value : BitVec 64) (member : parent∈live) (capacity : 64≤size parent)
 (tag : s.memory parent=.word (1#64)) (offset : Nat) (lower : 32≤offset) (upper : offset<64) :
 AllocatedTrieWorld (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value) live extensions branches size frontier ∧
 TrieNodeKinds (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value) live extensions branches := by
 have outside:=world.layout.leaf_field_not_owned s live extensions branches size kinds parent member capacity tag offset lower upper
 have frame : ∀address,TrieWalkRegistryWord live extensions branches address→
  (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value).memory address=s.memory address := by
  intro address owned
  have separate : address≠parent+BitVec.ofNat 64 offset:=by intro same;subst address;exact outside owned
  simp [sourceWriteWord,separate]
 refine ⟨⟨world.registry.after_word_frame frame,world.positive.after_registry_word_frame frame,
  world.layout,world.allocated,world.heap,world.capped,world.aligned⟩,?_⟩
 apply kinds.after_kind_frame world.layout.extensionLive world.layout.branchLive
 intro node registered
 exact frame node (Or.inl ⟨node,registered,rfl⟩)

#print axioms TrieNodeLayout.leaf_field_not_owned
#print axioms AllocatedTrieWorld.write_leaf_field
end InitECandidate.Runtime
