import InitECandidate.Runtime.FreshTrieNodeLayouts
import InitECandidate.Runtime.TriePositiveChildStore
import InitECandidate.Runtime.MptNewEmptyReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete invariant for the indexed trie: live child links, positive
extensions, disjoint allocated records and their actual heap frontier. -/
structure AllocatedTrieWorld {F : Type} (s : PanSemStateFiniteExact 64 F)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat) (frontier : BitVec 64) : Prop where
 registry : TrieWalkRegistry live extensions branches s
 positive : TriePositiveExtensions extensions s
 layout : TrieNodeLayout live extensions branches size
 allocated : ∀node∈live,node.toNat+size node≤frontier.toNat
 heap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word frontier))
 capped : frontier.toNat≤33806089496
 aligned : frontier.toNat%8=0

theorem AllocatedTrieWorld.owned_below {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier) :
 ∀address,TrieWalkRegistryWord live extensions branches address→address.toNat<frontier.toNat :=
 world.layout.owned_below frontier world.allocated

theorem MptNewEmptyReady.allocated_world {F : Type} {s post : PanSemStateFiniteExact 64 F}
 {name : MlS} {pointer : BitVec 64} (ready : MptNewEmptyReady s post name pointer) :
 AllocatedTrieWorld post ∅ ∅ ∅ (fun _=>0) (allocationEnd pointer 16) := by
 have layout : TrieNodeLayout ∅ ∅ ∅ (fun _=>0) := by
  constructor <;> simp
 refine ⟨ready.registry,TriePositiveExtensions.empty post,layout,?_,?_,ready.capped,ready.aligned⟩
 · intro node member;exact False.elim member
 · rw [ready.globals];simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem NodeNewLeafDeclarationReady.allocated_world {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length valuePointer valueLength : BitVec 64} {live extensions branches : Set (BitVec 64)}
 {size : BitVec 64 → Nat}
 (ready : NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer) :
 AllocatedTrieWorld post (insert pointer live) extensions branches
  (Function.update size pointer 64) (allocationEnd pointer 64) := by
 refine ⟨ready.registry,ready.positive_extensions world.positive world.owned_below,
  ready.layout world.layout world.allocated,
  trie_records_allocated_insert _ _ _ world.allocated ready.extent,?_,ready.capped,ready.aligned⟩
 rw [ready.globals];simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem NodeNewBranchDeclarationReady.allocated_world {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer : BitVec 64} {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewBranchDeclarationReady s post name pointer live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer) :
 AllocatedTrieWorld post (insert pointer live) extensions (insert pointer branches)
  (Function.update size pointer 176) (allocationEnd pointer 176) := by
 refine ⟨ready.registry,ready.positive_extensions world.positive world.owned_below,
  ready.layout world.layout world.allocated,
  trie_records_allocated_insert _ _ _ world.allocated ready.extent,?_,ready.capped,ready.aligned⟩
 rw [ready.globals];simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem NodeNewExtDeclarationReady.allocated_world {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {name : MlS}
 {pointer nib length child : BitVec 64} {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat}
 (ready : NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches)
 (world : AllocatedTrieWorld s live extensions branches size pointer) (nonzero : length≠0) :
 AllocatedTrieWorld post (insert pointer live) (insert pointer extensions) branches
  (Function.update size pointer 56) (allocationEnd pointer 56) := by
 refine ⟨ready.registry,ready.positive_extensions world.positive nonzero world.owned_below,
  ready.layout world.layout world.allocated,
  trie_records_allocated_insert _ _ _ world.allocated ready.extent,?_,ready.capped,ready.aligned⟩
 rw [ready.globals];simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem AllocatedTrieWorld.write_child {F : Type} {s : PanSemStateFiniteExact 64 F}
 {live extensions branches : Set (BitVec 64)} {size : BitVec 64 → Nat} {frontier : BitVec 64}
 (world : AllocatedTrieWorld s live extensions branches size frontier) (address child : BitVec 64)
 (childValid : child=0 ∨child∈live)
 (kindsSeparate : ∀node∈live,node≠address)
 (lengthsSeparate : ∀node∈extensions,node+40≠address) :
 AllocatedTrieWorld (sourceWriteWord s address child) live extensions branches size frontier := by
 obtain ⟨registry,positive⟩:=world.registry.write_positive_child s live extensions branches address child
  world.positive childValid kindsSeparate lengthsSeparate
 exact ⟨registry,positive,world.layout,world.allocated,world.heap,world.capped,world.aligned⟩

#print axioms MptNewEmptyReady.allocated_world
#print axioms NodeNewLeafDeclarationReady.allocated_world
#print axioms NodeNewBranchDeclarationReady.allocated_world
#print axioms NodeNewExtDeclarationReady.allocated_world
#print axioms AllocatedTrieWorld.write_child
end InitECandidate.Runtime
