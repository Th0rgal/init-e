import InitECandidate.Runtime.TrieAllocationFloorFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Any actual write confined to a valid branch child cell preserves all
stored key floors; branch records have no segment header. -/
theorem TrieAllocationFloor.after_branch_child {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64} {floor : Nat}
 (lower : TrieAllocationFloor s live branches floor)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent : BitVec 64) (member : parent∈branches) (index : Nat) (small : index<16)
 (frame : ∀watched,watched≠branchChildAddress parent index→post.memory watched=s.memory watched) :
 TrieAllocationFloor post live branches floor := by
 have address : branchChildAddress parent index=parent+BitVec.ofNat 64 (32+index*8) := by
  simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
 apply lower.after_record_fields paths world parent (world.layout.branchLive member) [32+index*8]
 · intro field included
   have equal : field=32+index*8:=by simpa using included
   rw [equal];have:=world.layout.branchSize parent member;omega
 · exact Or.inl member
 · intro watched separate
   apply frame
   rw [address]
   exact separate _ (by simp)

#print axioms TrieAllocationFloor.after_branch_child
end InitECandidate.Runtime
