import InitECandidate.Runtime.TrieAllocationFloorFrame
import InitECandidate.Runtime.TrieChildSlotPathsWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A concrete node-field store preserves the lower allocation boundary when
it avoids leaf/extension path headers. -/
theorem TrieAllocationFloor.after_node_field {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat} {frontier : BitVec 64} {floor : Nat}
 (lower : TrieAllocationFloor s live branches floor)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (parent value : BitVec 64) (member : parent∈live) (field : Nat) (inside : field<size parent)
 (headerSafe : parent∈branches ∨(field≠32 ∧field≠40)) :
 TrieAllocationFloor (sourceWriteWord s (parent+BitVec.ofNat 64 field) value) live branches floor := by
 apply lower.after_record_fields paths world parent member [field]
 · intro f included
   have same : f=field:=by simpa using included
   simpa [same] using inside
 · rcases headerSafe with branch|safe
   · exact Or.inl branch
   · right;intro f included
     have same : f=field:=by simpa using included
     simpa [same] using safe
 · intro watched separate
   have different : watched≠parent+BitVec.ofNat 64 field:=separate field (by simp)
   simp [sourceWriteWord,different]

/-- Both actual child-link forms preserve allocation floors: branch slots
have no stored path header, and extension links occupy offset 48. -/
theorem TrieChildSlot.write_allocation_floor {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 {frontier address : BitVec 64} {floor : Nat}
 (typed : TrieChildSlot s extensions branches address)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (paths : TrieNodePaths s live extensions branches size frontier)
 (lower : TrieAllocationFloor s live branches floor) (child : BitVec 64) :
 TrieAllocationFloor (sourceWriteWord s address child) live branches floor := by
 rcases typed with ⟨parent,member,index,small,rfl⟩ | ⟨parent,member,length,rfl,segment,positive⟩
 · have addressNat : branchChildAddress parent index=parent+BitVec.ofNat 64 (32+index*8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
   rw [addressNat]
   exact lower.after_node_field paths world parent child (world.layout.branchLive member) _
    (by have:=world.layout.branchSize parent member;omega) (Or.inl member)
 · exact lower.after_node_field paths world parent child (world.layout.extensionLive member) 48
    (by have:=world.layout.extensionSize parent member;omega) (Or.inr (by decide))

#print axioms TrieAllocationFloor.after_node_field
#print axioms TrieChildSlot.write_allocation_floor
end InitECandidate.Runtime
