import InitECandidate.Runtime.TrieNodeLayoutInsert
import InitECandidate.Runtime.FreshTrieRegistryWordBounds
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every observed registry word is inside its allocated record, hence below
the current heap frontier. This bridges full record separation to constructor
word-frame contracts. -/
theorem TrieNodeLayout.owned_below {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64 → Nat} (layout : TrieNodeLayout live extensions branches size)
 (frontier : BitVec 64) (allocated : ∀ node∈live,node.toNat+size node≤frontier.toNat) :
 ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<frontier.toNat := by
 intro address owned
 rcases owned with ⟨node,member,same⟩ | ⟨node,member,field⟩ | ⟨node,member,slot,small,same⟩
 · subst address
   have := allocated node member
   have := layout.positive node member
   omega
 · have liveNode:=layout.extensionLive member
   have extent:=layout.extensionSize node member
   have before:=allocated node liveNode
   rcases field with same|same
   · subst address;change (node+40#64).toNat<frontier.toNat;rw [layout.field_nat node liveNode 40 (by omega)];omega
   · subst address;change (node+48#64).toNat<frontier.toNat;rw [layout.field_nat node liveNode 48 (by omega)];omega
 · subst address
   have liveNode:=layout.branchLive member
   have extent:=layout.branchSize node member
   have before:=allocated node liveNode
   have address : branchChildAddress node slot=node+BitVec.ofNat 64 (32+slot*8) := by
    simp [branchChildAddress,BitVec.ofNat_add,BitVec.ofNat_mul,BitVec.add_assoc]
   rw [address,layout.field_nat node liveNode (32+slot*8) (by omega)]
   omega

theorem NodeNewLeafDeclarationReady.layout {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length valuePointer valueLength : BitVec 64} {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64 → Nat}
 (ready : NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches)
 (layout : TrieNodeLayout live extensions branches size)
 (allocated : ∀node∈live,node.toNat+size node≤pointer.toNat) :
 TrieNodeLayout (insert pointer live) extensions branches (Function.update size pointer 64) := by
 exact layout.insert_record pointer 64 (by decide) allocated
  (by have:=ready.extent;have:=ready.capped;omega)

theorem NodeNewExtDeclarationReady.layout {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child : BitVec 64} {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64 → Nat}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (layout : TrieNodeLayout live extensions branches size)
 (allocated : ∀node∈live,node.toNat+size node≤pointer.toNat) :
 TrieNodeLayout (insert pointer live) (insert pointer extensions) branches (Function.update size pointer 56) := by
 exact layout.insert_extension pointer 56 (by decide) allocated
  (by have:=ready.extent;have:=ready.capped;omega)

theorem NodeNewBranchDeclarationReady.layout {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer : BitVec 64} {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (layout : TrieNodeLayout live extensions branches size)
 (allocated : ∀node∈live,node.toNat+size node≤pointer.toNat) :
 TrieNodeLayout (insert pointer live) extensions (insert pointer branches) (Function.update size pointer 176) := by
 exact layout.insert_branch pointer 176 (by decide) allocated
  (by have:=ready.extent;have:=ready.capped;omega)

/-- Extending a frontier by the constructor's earned extent retains all old
record endpoints and includes the new record. -/
theorem trie_records_allocated_insert {live : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (pointer finish : BitVec 64) (bytes : Nat)
 (allocated : ∀node∈live,node.toNat+size node≤pointer.toNat)
 (extent : pointer.toNat+bytes≤finish.toNat) :
 ∀node∈insert pointer live,node.toNat+Function.update size pointer bytes node≤finish.toNat := by
 classical
 intro node member
 by_cases same : node=pointer
 · subst node;simpa using extent
 · have old : node∈live := member.resolve_left same
   have := allocated node old
   simp only [Function.update_of_ne same]
   omega

#print axioms TrieNodeLayout.owned_below
#print axioms NodeNewLeafDeclarationReady.layout
#print axioms NodeNewExtDeclarationReady.layout
#print axioms NodeNewBranchDeclarationReady.layout
#print axioms trie_records_allocated_insert
end InitECandidate.Runtime
