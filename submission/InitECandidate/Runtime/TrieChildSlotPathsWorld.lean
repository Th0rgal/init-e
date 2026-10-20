import InitECandidate.Runtime.TrieNodePathsStore
import InitECandidate.Runtime.AllocatedTrieChildKinds
import InitECandidate.Runtime.TrieChildSlotPreservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Replacing any typed child backlink by a live/null result preserves the
full allocated world, exact kinds, stored paths and separated input paths.
Both the branch slot and positive-extension field are handled concretely. -/
theorem TrieChildSlot.write_paths_world {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier address : BitVec 64}
 (typed : TrieChildSlot s extensions branches address)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (child : BitVec 64) (valid : child=0 ∨child∈live) :
 AllocatedTrieWorld (sourceWriteWord s address child) live extensions branches size frontier ∧
 TrieNodeKinds (sourceWriteWord s address child) live extensions branches ∧
 TrieNodePaths (sourceWriteWord s address child) live extensions branches size frontier ∧
 (∀key len,TriePathBuffer s live size key len frontier→
  TriePathBuffer (sourceWriteWord s address child) live size key len frontier) := by
 have lengths:=typed.length_separate s live extensions branches size world.layout address
 rcases typed with ⟨parent,member,index,small,rfl⟩ | ⟨parent,member,length,rfl,segment,positive⟩
 · obtain ⟨worldOut,kindsOut⟩:=world.write_branch_child_kinds kinds parent child member index small valid
   have addressNat : branchChildAddress parent index=parent+BitVec.ofNat 64 (32+index*8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
   refine ⟨worldOut,kindsOut,?_,?_⟩
   · rw [addressNat]
     exact paths.after_node_field world parent child (world.layout.branchLive member) _
      (by have:=world.layout.branchSize parent member;omega) (Or.inl member)
   · intro key len path
     rw [addressNat]
     exact path.after_node_field world.layout parent child (world.layout.branchLive member) _
      (by have:=world.layout.branchSize parent member;omega)
 · have parentLive:=world.layout.extensionLive member
   have capacity:=world.layout.extensionSize parent member
   have separate : ∀node∈live,node≠parent+48#64 := by
    intro node registered
    simpa using world.layout.fields_ne node parent registered parentLive 0 48
     (world.layout.positive node registered) (by omega) (Or.inr (by decide))
   obtain ⟨worldOut,kindsOut⟩:=world.write_child_kinds kinds (parent+48#64) child valid separate lengths
   refine ⟨worldOut,kindsOut,?_,?_⟩
   · exact paths.after_node_field world parent child parentLive 48 (by omega) (Or.inr (by decide))
   · intro key len path
     exact path.after_node_field world.layout parent child parentLive 48 (by omega)

#print axioms TrieChildSlot.write_paths_world
end InitECandidate.Runtime
