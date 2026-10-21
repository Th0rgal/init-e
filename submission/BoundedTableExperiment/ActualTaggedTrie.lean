import ActualLiveTrieInvariant

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact

set_option maxHeartbeats 1000000

/-- The candidate guard treats `node <= cap` as a leaf/empty slot; internal
nodes are exactly those above the cap threshold (unsigned). -/
def IsInternal (cap node : BitVec 64) : Prop := BitVec.ult cap node

/-- Tagged reachability: an edge may only be taken from an internal parent. -/
inductive ReachableInternal {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cap root : BitVec 64) : BitVec 64 -> Prop
  | root : ReachableInternal s cap root root
  | left {p l r route} :
      ReachableInternal s cap root p -> IsInternal cap p ->
      NodeLinkInv s p l r route -> ReachableInternal s cap root l
  | right {p l r route} :
      ReachableInternal s cap root p -> IsInternal cap p ->
      NodeLinkInv s p l r route -> ReachableInternal s cap root r

/-- Corrected live-edge invariant: root may be empty/leaf; route obligations
apply only to tagged internal nodes. -/
structure TaggedTrieInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (root cap : BitVec 64) (keyLen : Nat) : Prop where
  rootCase : root = 0 ∨ IsInternal cap root
  rootLink : IsInternal cap root → ∃ left right route, NodeLinkInv s root left right route
  routeBound : ∀ p l r route,
    ReachableInternal s cap root p -> IsInternal cap p -> NodeLinkInv s p l r route ->
      routeBit route < 8 * keyLen
  childGreater : ∀ p l r route c,
    ReachableInternal s cap root p -> IsInternal cap p -> NodeLinkInv s p l r route ->
    (c = l ∨ c = r) -> IsInternal cap c ->
    ∀ lc rc rcRoute, NodeLinkInv s c lc rc rcRoute ->
      routeBit route < routeBit rcRoute

/-- A tagged internal root has a concrete node record and route bound. -/
theorem TaggedTrieInv.rootBound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root cap : BitVec 64} {keyLen : Nat} (trie : TaggedTrieInv s root cap keyLen)
    (hroot : IsInternal cap root) :
    ∃ left right route, NodeLinkInv s root left right route ∧
      routeBit route < 8 * keyLen := by
  obtain ⟨l, r, route, link⟩ := trie.rootLink hroot
  exact ⟨l, r, route, link,
    trie.routeBound root l r route (ReachableInternal.root) hroot link⟩

theorem TaggedTrieInv.childBound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root cap : BitVec 64} {keyLen : Nat} (trie : TaggedTrieInv s root cap keyLen)
    {p : BitVec 64} (reach : ReachableInternal s cap root p) (hint : IsInternal cap p)
    {l r route : BitVec 64} (link : NodeLinkInv s p l r route) :
    routeBit route < 8 * keyLen :=
  trie.routeBound p l r route reach hint link

/-- One tagged live-edge step. -/
theorem TaggedTrieInv.step {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root cap : BitVec 64} {keyLen : Nat} (trie : TaggedTrieInv s root cap keyLen)
    {p l r route c : BitVec 64} (reach : ReachableInternal s cap root p)
    (hint : IsInternal cap p) (link : NodeLinkInv s p l r route)
    (hc : c = l ∨ c = r) (hcint : IsInternal cap c)
    {cl cr rc : BitVec 64} (childLink : NodeLinkInv s c cl cr rc) :
    ReachableInternal s cap root c ∧ routeBit route < routeBit rc := by
  have hreach : ReachableInternal s cap root c := by
    rcases hc with h | h
    · rw [h]; exact ReachableInternal.left reach hint link
    · rw [h]; exact ReachableInternal.right reach hint link
  exact ⟨hreach, trie.childGreater p l r route c reach hint link hc hcint cl cr rc childLink⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.TaggedTrieInv.rootBound
#print axioms BoundedTableExperiment.TaggedTrieInv.childBound
#print axioms BoundedTableExperiment.TaggedTrieInv.step
