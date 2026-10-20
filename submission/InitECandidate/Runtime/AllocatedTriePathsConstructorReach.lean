import InitECandidate.Runtime.AllocatedTrieConstructorReach
import InitECandidate.Runtime.FreshTrieNodeKinds
import InitECandidate.Runtime.FreshTrieNodePaths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/- Actual original constructor prefixes carrying allocated world, exact tags
and every stored segment. Allocation failures are included by Reaches. -/
theorem allocated_trie_leaf_paths_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (pointer nib length valuePointer valueLength : BitVec 64)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size nib length pointer) (short : length.toNat≤18)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word valuePointer),.val (.word valueLength)])
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_leaf") arguments tail)
  (fun post=>NodeNewLeafDeclarationReady s post name pointer nib length valuePointer valueLength live extensions branches ∧
   AllocatedTrieWorld post (insert pointer live) extensions branches
    (Function.update size pointer 64) (allocationEnd pointer 64) ∧
   TrieNodeKinds post (insert pointer live) extensions branches ∧
   TrieNodePaths post (insert pointer live) extensions branches (Function.update size pointer 64) (allocationEnd pointer 64)) 3 tail := by
 have reached:=allocated_trie_leaf_reaches s name arguments tail pointer nib length valuePointer valueLength live extensions branches size world args fullDomain code budget
 apply reaches_mono s _ tail _ _ 3 3 (le_refl _) _ reached
 intro post facts
 obtain ⟨ready,worldOut⟩:=facts
 exact ⟨ready,worldOut,ready.node_kinds world kinds,ready.node_paths world paths keyPath short⟩

#print axioms allocated_trie_leaf_paths_reaches

theorem allocated_trie_branch_paths_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (tail : ProgHOL 64) (pointer : BitVec 64)
 (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 41≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_branch") [] tail)
  (fun post=>NodeNewBranchDeclarationReady s post name pointer live extensions branches ∧
   AllocatedTrieWorld post (insert pointer live) extensions (insert pointer branches)
    (Function.update size pointer 176) (allocationEnd pointer 176) ∧
   TrieNodeKinds post (insert pointer live) extensions (insert pointer branches) ∧
   TrieNodePaths post (insert pointer live) extensions (insert pointer branches) (Function.update size pointer 176) (allocationEnd pointer 176)) 41 tail := by
 have reached:=allocated_trie_branch_reaches s name tail pointer live extensions branches size world fullDomain code budget
 apply reaches_mono s _ tail _ _ 41 41 (le_refl _) _ reached
 intro post facts
 obtain ⟨ready,worldOut⟩:=facts
 exact ⟨ready,worldOut,ready.node_kinds world kinds,ready.node_paths world paths⟩

#print axioms allocated_trie_branch_paths_reaches

theorem allocated_trie_extension_paths_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
 (pointer nib length child : BitVec 64) (live extensions branches : Set (BitVec 64)) (size : BitVec 64 → Nat)
 (world : AllocatedTrieWorld s live extensions branches size pointer)
 (kinds : TrieNodeKinds s live extensions branches)
 (paths : TrieNodePaths s live extensions branches size pointer)
 (keyPath : TriePathBuffer s live size nib length pointer) (short : length.toNat≤18)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=
  some [.val (.word nib),.val (.word length),.val (.word child)])
 (childValid : child=0 ∨child∈live) (nonzero : length≠0)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (code : s.code=originalRuntimeCode) (budget : 3≤s.clock) :
 Reaches s (.decCall name .one (ofString "node_new_ext") arguments tail)
  (fun post=>NodeNewExtDeclarationReady s post name pointer nib length child live extensions branches ∧
   AllocatedTrieWorld post (insert pointer live) (insert pointer extensions) branches
    (Function.update size pointer 56) (allocationEnd pointer 56) ∧
   TrieNodeKinds post (insert pointer live) (insert pointer extensions) branches ∧
   TrieNodePaths post (insert pointer live) (insert pointer extensions) branches (Function.update size pointer 56) (allocationEnd pointer 56)) 3 tail := by
 have reached:=allocated_trie_extension_reaches s name arguments tail pointer nib length child live extensions branches size world args childValid nonzero fullDomain code budget
 apply reaches_mono s _ tail _ _ 3 3 (le_refl _) _ reached
 intro post facts
 obtain ⟨ready,worldOut⟩:=facts
 exact ⟨ready,worldOut,ready.node_kinds world kinds,ready.node_paths world paths keyPath short⟩

#print axioms allocated_trie_extension_paths_reaches

end InitECandidate.Runtime
