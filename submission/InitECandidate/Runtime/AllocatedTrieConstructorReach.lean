import InitECandidate.Runtime.AllocatedTrieWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual leaf construction maintains the whole indexed-trie allocation
invariant, deriving all old-word bounds from record ownership. -/
theorem allocated_trie_leaf_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (pointer nib length valuePointer valueLength : BitVec 64)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word valuePointer),.val (.word valueLength)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_leaf") arguments tail)
  (fun post=>NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches ∧
   AllocatedTrieWorld post (insert pointer live) extensions branches
    (Function.update size pointer 64) (allocationEnd pointer 64)) 3 tail := by
 apply reaches_mono s _ tail _ _ 3 3 (by omega)
  (fun post ready=>⟨ready,ready.allocated_world world⟩)
 exact node_new_leaf_registry_declaration_reaches s name arguments tail pointer nib length valuePointer valueLength
  live extensions branches args world.heap world.capped fullDomain world.registry world.owned_below code budget

theorem allocated_trie_branch_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (tail : ProgHOL 64) (pointer : BitVec 64)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 41≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_branch") [] tail)
  (fun post=>NodeNewBranchDeclarationReady s post name pointer live extensions branches ∧
   AllocatedTrieWorld post (insert pointer live) extensions (insert pointer branches)
    (Function.update size pointer 176) (allocationEnd pointer 176)) 41 tail := by
 apply reaches_mono s _ tail _ _ 41 41 (by omega)
  (fun post ready=>⟨ready,ready.allocated_world world⟩)
 exact node_new_branch_registry_declaration_reaches s name tail pointer live extensions branches
  world.heap world.capped world.aligned fullDomain world.registry world.owned_below code budget

/-- The actual indexed constructors call node_new_ext only for positive
segments. This yields a world that remains valid when a later insertion
replaces its child with a freshly allocated node. -/
theorem allocated_trie_extension_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (pointer nib length child : BitVec 64) (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word child)])
 (childValid : child=0 ∨child∈live) (nonzero : length≠0)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_ext") arguments tail)
  (fun post=>NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches ∧
   AllocatedTrieWorld post (insert pointer live) (insert pointer extensions) branches
    (Function.update size pointer 56) (allocationEnd pointer 56)) 3 tail := by
 apply reaches_mono s _ tail _ _ 3 3 (by omega)
  (fun post ready=>⟨ready,ready.allocated_world world nonzero⟩)
 exact node_new_ext_registry_declaration_reaches s name arguments tail pointer nib length child live extensions branches
  args world.heap world.capped fullDomain world.registry world.owned_below childValid (Or.inl nonzero) code budget

#print axioms allocated_trie_leaf_reaches
#print axioms allocated_trie_branch_reaches
#print axioms allocated_trie_extension_reaches
end InitECandidate.Runtime
