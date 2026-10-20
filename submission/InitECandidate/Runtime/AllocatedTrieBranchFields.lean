import InitECandidate.Runtime.AllocatedTrieLeafFields
import InitECandidate.Runtime.TrieBranchValueStore
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Branch payload fields follow all sixteen child slots, so a concrete value
store cannot change any traversal field, including those of other records. -/
theorem TrieNodeLayout.branch_value_not_owned
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (layout : TrieNodeLayout live extensions branches size)
 (parent : BitVec 64) (member : parent∈branches)
 (offset : Nat) (lower : 160≤offset) (upper : offset<176) :
 ¬TrieWalkRegistryWord live extensions branches (parent+BitVec.ofNat 64 offset) := by
 have separate (node : BitVec 64) (registered : node∈live) (field : Nat)
  (inside : field<size node) (different : field≠offset) :
  parent+BitVec.ofNat 64 offset≠node+BitVec.ofNat 64 field :=
  layout.fields_ne parent node (layout.branchLive member) registered offset field
   (by have:=layout.branchSize parent member;omega) inside (Or.inr (Ne.symm different))
 rintro (⟨node,registered,equal⟩|⟨node,registered,atLength|atChild⟩|⟨node,registered,index,inside,equal⟩)
 · exact separate node registered 0 (layout.positive node registered) (by omega) (by simpa using equal)
 · exact separate node (layout.extensionLive registered) 40
    (by have:=layout.extensionSize node registered;omega) (by omega) atLength
 · exact separate node (layout.extensionLive registered) 48
    (by have:=layout.extensionSize node registered;omega) (by omega) atChild
 · have address : branchChildAddress node index=node+BitVec.ofNat 64 (32+index*8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
   rw [address] at equal
   exact separate node (layout.branchLive registered) (32+index*8)
    (by have:=layout.branchSize node registered;omega) (by omega) equal

/-- Updating a branch value preserves allocated records, positive extensions,
all child links and exact node kinds; the value itself is unrestricted. -/
theorem AllocatedTrieWorld.write_branch_field {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (parent value : BitVec 64) (member : parent∈branches)
 (offset : Nat) (lower : 160≤offset) (upper : offset<176) :
 AllocatedTrieWorld (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value) live extensions branches size frontier ∧
 TrieNodeKinds (sourceWriteWord s (parent+BitVec.ofNat 64 offset) value) live extensions branches := by
 have outside:=world.layout.branch_value_not_owned live extensions branches size parent member offset lower upper
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

#print axioms TrieNodeLayout.branch_value_not_owned
#print axioms AllocatedTrieWorld.write_branch_field
end InitECandidate.Runtime
