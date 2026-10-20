import InitECandidate.Runtime.NodeNewLeafRegistryReach
import InitECandidate.Runtime.NodeNewBranchRegistryReach
import InitECandidate.Runtime.NodeNewExtRegistryReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem fresh_offset_below (pointer finish : BitVec 64) (size offset : Nat)
 (extent : pointer.toNat+size≤finish.toNat) (small : offset<size) :
 (pointer+BitVec.ofNat 64 offset).toNat<finish.toNat := by
 have cap:=finish.isLt
 rw [BitVec.toNat_add,BitVec.toNat_ofNat]
 omega

/-- A real fresh terminal allocation keeps all registry-observed words below
the new frontier, so the next constructor can protect them in turn. -/
theorem NodeNewLeafDeclarationReady.owned_below {F : Type} {base next : PanSemStateFiniteExact 64 F}
 {name : MlS} {pointer nib length valuePointer valueLength : BitVec 64} {live extensions branches : Set (BitVec 64)}
 (ready : NodeNewLeafDeclarationReady base next name pointer nib length valuePointer valueLength live extensions branches)
 (old : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat) :
 ∀address,TrieWalkRegistryWord (insert pointer live) extensions branches address→
  address.toNat<(allocationEnd pointer 64).toNat := by
 intro address owned
 rcases owned with ⟨node,member,sameAddress⟩|extension|branch
 · subst address
   rcases Set.mem_insert_iff.mp member with sameNode|member
   · subst node
     have := ready.extent;omega
   · have := old node (Or.inl ⟨node,member,rfl⟩);have := ready.extent;omega
 · have := old address (Or.inr (Or.inl extension));have := ready.extent;omega
 · have := old address (Or.inr (Or.inr branch));have := ready.extent;omega

theorem NodeNewExtDeclarationReady.owned_below {F : Type} {base next : PanSemStateFiniteExact 64 F}
 {name : MlS} {pointer nib length child : BitVec 64} {live extensions branches : Set (BitVec 64)}
 (ready : NodeNewExtDeclarationReady base next name pointer nib length child live extensions branches)
 (old : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat) :
 ∀address,TrieWalkRegistryWord (insert pointer live) (insert pointer extensions) branches address→
  address.toNat<(allocationEnd pointer 56).toNat := by
 intro address owned
 rcases owned with ⟨node,member,sameAddress⟩|⟨node,member,offset⟩|branch
 · subst address
   rcases Set.mem_insert_iff.mp member with sameNode|member
   · subst node
     have := ready.extent;omega
   · have := old node (Or.inl ⟨node,member,rfl⟩);have := ready.extent;omega
 · rcases Set.mem_insert_iff.mp member with sameNode|member
   · subst node
     rcases offset with sameAddress|sameAddress
     · subst address
       exact fresh_offset_below pointer _ 56 40 ready.extent (by decide)
     · subst address
       exact fresh_offset_below pointer _ 56 48 ready.extent (by decide)
   · have := old address (Or.inr (Or.inl ⟨node,member,offset⟩));have := ready.extent;omega
 · have := old address (Or.inr (Or.inr branch));have := ready.extent;omega

theorem NodeNewBranchDeclarationReady.owned_below {F : Type} {base next : PanSemStateFiniteExact 64 F}
 {name : MlS} {pointer : BitVec 64} {live extensions branches : Set (BitVec 64)}
 (ready : NodeNewBranchDeclarationReady base next name pointer live extensions branches)
 (old : ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<pointer.toNat) :
 ∀address,TrieWalkRegistryWord (insert pointer live) extensions (insert pointer branches) address→
  address.toNat<(allocationEnd pointer 176).toNat := by
 intro address owned
 rcases owned with ⟨node,member,sameAddress⟩|extension|⟨node,member,slot,small,sameAddress⟩
 · subst address
   rcases Set.mem_insert_iff.mp member with sameNode|member
   · subst node
     have := ready.extent;omega
   · have := old node (Or.inl ⟨node,member,rfl⟩);have := ready.extent;omega
 · have := old address (Or.inr (Or.inl extension));have := ready.extent;omega
 · subst address
   rcases Set.mem_insert_iff.mp member with sameNode|member
   · subst node
     have equal : branchChildAddress pointer slot=pointer+BitVec.ofNat 64 (32+slot*8) := by
      unfold branchChildAddress
      bv_omega
     rw [equal]
     exact fresh_offset_below pointer _ 176 (32+slot*8) ready.extent (by omega)
   · have := old (branchChildAddress node slot) (Or.inr (Or.inr ⟨node,member,slot,small,rfl⟩))
     have := ready.extent;omega

#print axioms NodeNewLeafDeclarationReady.owned_below
#print axioms NodeNewExtDeclarationReady.owned_below
#print axioms NodeNewBranchDeclarationReady.owned_below
end InitECandidate.Runtime
