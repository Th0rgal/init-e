import InitECandidate.Runtime.AllocatedTrieMetadata
import InitECandidate.Runtime.TrieChildSlotPreservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An actual extension/branch backlink cannot alias cache metadata in any
allocated trie record, including a backlink into the same record. -/
theorem TrieChildSlot.metadata_separate {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (layout : TrieNodeLayout live extensions branches size) (slot node : BitVec 64)
 (typed : TrieChildSlot s extensions branches slot) (member : node∈live) (capacity : 32≤size node)
 (offset : Nat) (small : offset<32) : slot≠node+BitVec.ofNat 64 offset := by
 rcases typed with ⟨parent,registered,index,inside,rfl⟩|⟨parent,registered,length,rfl,_,_⟩
 · have address : branchChildAddress parent index=parent+BitVec.ofNat 64 (32+index*8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
   rw [address]
   apply layout.fields_ne parent node (layout.branchLive registered) member (32+index*8) offset
   · have:=layout.branchSize parent registered;omega
   · omega
   · exact Or.inr (by omega)
 · apply layout.fields_ne parent node (layout.extensionLive registered) member 48 offset
   · have:=layout.extensionSize parent registered;omega
   · omega
   · exact Or.inr (by omega)

/-- Allocated record extents bound the actual extension/branch child address,
so the challenge-wide domain supplies its real commit-store access. -/
theorem TrieChildSlot.allocated_below {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier slot : BitVec 64)
 (world : AllocatedTrieWorld s live extensions branches size frontier)
 (typed : TrieChildSlot s extensions branches slot) : slot.toNat<frontier.toNat := by
 rcases typed with ⟨parent,registered,index,inside,rfl⟩|⟨parent,registered,length,rfl,_,_⟩
 · have address : branchChildAddress parent index=parent+BitVec.ofNat 64 (32+index*8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
   have member:=world.layout.branchLive registered
   have capacity:=world.layout.branchSize parent registered
   have bound:=world.allocated parent member
   rw [address,world.layout.field_nat parent member (32+index*8) (by omega)]
   omega
 · have member:=world.layout.extensionLive registered
   have capacity:=world.layout.extensionSize parent registered
   have bound:=world.allocated parent member
   rw [world.layout.field_nat parent member 48 (by omega)]
   omega

#print axioms TrieChildSlot.metadata_separate
#print axioms TrieChildSlot.allocated_below
end InitECandidate.Runtime
