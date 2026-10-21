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

/-- Empty (`0`) or a nonempty leaf ID in `1..cap`. -/
def IsLeafOrEmpty (cap node : BitVec 64) : Prop := node.toNat ≤ cap.toNat

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

/-- Corrected live-edge invariant: root may be empty, a valid nonempty leaf
ID (`1..cap`), or an internal node; route obligations apply only to tagged
internal nodes. -/
structure TaggedTrieInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (root cap : BitVec 64) (keyLen : Nat) : Prop where
  rootCase : IsLeafOrEmpty cap root ∨ IsInternal cap root
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

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact

/-- Post-store internal reachability away from the stored cell is pre-store
internal reachability. -/
theorem ReachableInternal.of_store_other {F : Type} {s : PanSemStateFiniteExact 64 F}
    {cap root watched : BitVec 64} (value : HolWordLab 64)
    {postMem : BitVec 64 → HolWordLab 64}
    (store : @panMemStoresHOL 64 _ watched [value]
      s.memaddrs (Classical.decPred _) s.memory = some postMem)
    (separate : ∀ p, ReachableInternal s cap root p ->
      p ≠ watched ∧ p + 8 ≠ watched ∧ p + 16 ≠ watched)
    {p : BitVec 64}
    (reach : ReachableInternal { s with memory := postMem } cap root p) :
    ReachableInternal s cap root p := by
  induction reach with
  | root => exact ReachableInternal.root
  | left reach hint link ih =>
      obtain ⟨sep0, sep8, sep16⟩ := separate _ ih
      exact ReachableInternal.left ih hint (link.of_store_other value sep0 sep8 sep16 store)
  | right reach hint link ih =>
      obtain ⟨sep0, sep8, sep16⟩ := separate _ ih
      exact ReachableInternal.right ih hint (link.of_store_other value sep0 sep8 sep16 store)

/-- A store outside all tagged node cells preserves the corrected invariant. -/
theorem TaggedTrieInv.store_other {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root cap : BitVec 64} {keyLen : Nat} (trie : TaggedTrieInv s root cap keyLen)
    {watched : BitVec 64} (value : HolWordLab 64)
    {postMem : BitVec 64 → HolWordLab 64}
    (store : @panMemStoresHOL 64 _ watched [value]
      s.memaddrs (Classical.decPred _) s.memory = some postMem)
    (separate : ∀ p, ReachableInternal s cap root p ->
      p ≠ watched ∧ p + 8 ≠ watched ∧ p + 16 ≠ watched) :
    TaggedTrieInv { s with memory := postMem } root cap keyLen := by
  constructor
  · exact trie.rootCase
  · intro hroot
    obtain ⟨l, r, route, link⟩ := trie.rootLink hroot
    obtain ⟨sep0, sep8, sep16⟩ := separate root (ReachableInternal.root)
    exact ⟨l, r, route, link.store_other value sep0 sep8 sep16 store⟩
  · intro p l r route reach hint link
    have reachOld := ReachableInternal.of_store_other value store separate reach
    obtain ⟨sep0, sep8, sep16⟩ := separate p reachOld
    exact trie.routeBound p l r route reachOld hint
      (link.of_store_other value sep0 sep8 sep16 store)
  · intro p l r route c reach hint link hc hcint lc rc rcRoute childLink
    have reachOld := ReachableInternal.of_store_other value store separate reach
    obtain ⟨sep0, sep8, sep16⟩ := separate p reachOld
    have linkOld := link.of_store_other value sep0 sep8 sep16 store
    have hreachC : ReachableInternal s cap root c := by
      rcases hc with h | h
      · rw [h]; exact ReachableInternal.left reachOld hint linkOld
      · rw [h]; exact ReachableInternal.right reachOld hint linkOld
    obtain ⟨csep0, csep8, csep16⟩ := separate c hreachC
    have childOld := childLink.of_store_other value csep0 csep8 csep16 store
    exact trie.childGreater p l r route c reachOld hint linkOld hc hcint lc rc rcRoute childOld

end BoundedTableExperiment

#print axioms BoundedTableExperiment.ReachableInternal.of_store_other
#print axioms BoundedTableExperiment.TaggedTrieInv.store_other

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual child selection plus tagged live-edge ordering.  A leaf child has no
route obligation; the route conclusion is only for an internal child. -/
theorem candidateFindLeafChild_descent_tagged {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {root cap node left right route b m : BitVec 64} {keyLen : Nat}
    (trie : TaggedTrieInv s root cap keyLen)
    (reach : ReachableInternal s cap root node)
    (hint : IsInternal cap node)
    (run : StatementRun fn s candidateFindLeafChild none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node)))
    (bLocal : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (mLocal : s.locals.lookup (ofString "m") = some (.val (.word m)))
    {child : BitVec 64} {cl cr childRoute : BitVec 64}
    (childLink : NodeLinkInv s child cl cr childRoute)
    (childEq : child = if b &&& m = 0 then left else right) :
    post.locals.lookup (ofString "node") = some (.val (.word child)) ∧
      (IsInternal cap child → routeBit route < routeBit childRoute) := by
  obtain ⟨flag, guardEvents, branchEvents, eventsEq, guard, flagEq, nodeLookup,
    memEq, domRight, domLeft⟩ :=
    candidateFindLeafChild_links run inv nodeLocal bLocal mLocal
  have hc : child = left ∨ child = right := by
    by_cases hz : b &&& m = 0
    · exact Or.inl (by rw [childEq]; exact if_pos (by simpa using hz))
    · exact Or.inr (by rw [childEq]; exact if_neg (by simpa using hz))
  refine ⟨by simpa [childEq] using nodeLookup, ?_⟩
  intro hchildInt
  exact (trie.step reach hint inv hc hchildInt childLink).2

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeafChild_descent_tagged
