import InitECandidate.Runtime.TrieOwnedLeafAllocation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The actual constructor extends ownership while retaining every old
record and stored-key cell. New record/path facts come from its concrete ready witness. -/
theorem NodeNewExtDeclarationReady.owned_footprint_extension {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer) :
 TrieOwnedFootprint s.memory live branches size⊆
 TrieOwnedFootprint post.memory (insert pointer live) branches (Function.update size pointer 56) := by
 classical
 have different (node : BitVec 64) (member : node∈live) : node≠pointer := by
  intro same;subst node
  have:=world.layout.positive pointer member
  have:=world.allocated pointer member
  omega
 have headerFrame (node : BitVec 64) (member : node∈live) (nonBranch : node∉branches)
  (offset : Nat) (small : offset<48) :
  post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  apply ready.memory
  have capacity:=paths.header_capacity world.layout node member nonBranch
  rw [world.layout.field_nat node member offset (by omega)]
  have:=world.allocated node member
  omega
 apply trieOwnedFootprint_extend (fun _ h=>Or.inr h)
 · intro node member
   simp [Function.update_of_ne (different node member)]
 · intro node member nonBranch;exact nonBranch
 · intro node member nonBranch
   exact ⟨headerFrame node member nonBranch 32 (by decide),headerFrame node member nonBranch 40 (by decide)⟩


#print axioms NodeNewExtDeclarationReady.owned_footprint_extension

/-- The actual constructor extends ownership while retaining every old
record and stored-key cell. New record/path facts come from its concrete ready witness. -/
theorem NodeNewBranchDeclarationReady.owned_footprint_extension {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer : BitVec 64}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64→Nat}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (paths : TrieNodePaths s live extensions branches size pointer) :
 TrieOwnedFootprint s.memory live branches size⊆
 TrieOwnedFootprint post.memory (insert pointer live) (insert pointer branches) (Function.update size pointer 176) := by
 classical
 have different (node : BitVec 64) (member : node∈live) : node≠pointer := by
  intro same;subst node
  have:=world.layout.positive pointer member
  have:=world.allocated pointer member
  omega
 have headerFrame (node : BitVec 64) (member : node∈live) (nonBranch : node∉branches)
  (offset : Nat) (small : offset<48) :
  post.memory (node+BitVec.ofNat 64 offset)=s.memory (node+BitVec.ofNat 64 offset) := by
  apply ready.memory
  have capacity:=paths.header_capacity world.layout node member nonBranch
  rw [world.layout.field_nat node member offset (by omega)]
  have:=world.allocated node member
  omega
 apply trieOwnedFootprint_extend (fun _ h=>Or.inr h)
 · intro node member
   simp [Function.update_of_ne (different node member)]
 · intro node member nonBranch included
   rcases included with equal|old
   · exact different node member equal
   · exact nonBranch old
 · intro node member nonBranch
   exact ⟨headerFrame node member nonBranch 32 (by decide),headerFrame node member nonBranch 40 (by decide)⟩


#print axioms NodeNewBranchDeclarationReady.owned_footprint_extension
end InitECandidate.Runtime
