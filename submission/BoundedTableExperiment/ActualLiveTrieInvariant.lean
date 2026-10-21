import ActualLoadBridge
import ActualRouteDepthBound

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000

/-- Actual reachability through `NodeLinkInv` child words. -/
inductive Reachable {F : Type} (s : PanSemStateFiniteExact 64 F) :
    BitVec 64 -> BitVec 64 -> Prop
  | root (root : BitVec 64) : Reachable s root root
  | left {root p l r route} :
      Reachable s root p -> NodeLinkInv s p l r route -> Reachable s root l
  | right {root p l r route} :
      Reachable s root p -> NodeLinkInv s p l r route -> Reachable s root r

/-- One global live-edge invariant over actual node words. -/
structure TrieInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (root : BitVec 64) (keyLen : Nat) : Prop where
  rootLink : ∃ left right route, NodeLinkInv s root left right route
  routeBound : ∀ p l r route,
    Reachable s root p -> NodeLinkInv s p l r route -> routeBit route < 8 * keyLen
  childGreater : ∀ p l r route c,
    Reachable s root p -> NodeLinkInv s p l r route -> (c = l ∨ c = r) ->
    ∀ lc rc rcRoute, NodeLinkInv s c lc rc rcRoute ->
      routeBit route < routeBit rcRoute

theorem TrieInv.rootBound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root : BitVec 64} {keyLen : Nat} (trie : TrieInv s root keyLen) :
    ∃ left right route, NodeLinkInv s root left right route ∧
      routeBit route < 8 * keyLen := by
  obtain ⟨l, r, route, link⟩ := trie.rootLink
  exact ⟨l, r, route, link, trie.routeBound root l r route (Reachable.root root) link⟩

theorem TrieInv.childBound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root : BitVec 64} {keyLen : Nat} (trie : TrieInv s root keyLen)
    {p : BitVec 64} (reach : Reachable s root p)
    {l r route : BitVec 64} (link : NodeLinkInv s p l r route) :
    routeBit route < 8 * keyLen :=
  trie.routeBound p l r route reach link

/-- Actual child selection plus the live-edge ordering fact. -/
theorem candidateFindLeafChild_descent {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {root node left right route b m : BitVec 64} {keyLen : Nat}
    (trie : TrieInv s root keyLen)
    (reach : Reachable s root node)
    (run : StatementRun fn s candidateFindLeafChild none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node)))
    (bLocal : s.locals.lookup (ofString "b") = some (.val (.word b)))
    (mLocal : s.locals.lookup (ofString "m") = some (.val (.word m)))
    {child : BitVec 64} {cl cr childRoute : BitVec 64}
    (childLink : NodeLinkInv s child cl cr childRoute)
    (childEq : child = if b &&& m = 0 then left else right) :
    post.locals.lookup (ofString "node") = some (.val (.word child)) ∧
      routeBit route < routeBit childRoute := by
  obtain ⟨flag, guardEvents, branchEvents, eventsEq, guard, flagEq, nodeLookup,
    memEq, domRight, domLeft⟩ :=
    candidateFindLeafChild_links run inv nodeLocal bLocal mLocal
  have hc : child = left ∨ child = right := by
    by_cases hz : b &&& m = 0
    · exact Or.inl (by rw [childEq]; exact if_pos (by simpa using hz))
    · exact Or.inr (by rw [childEq]; exact if_neg (by simpa using hz))
  have hreach : Reachable s root child := by
    rcases hc with h | h
    · rw [h]; exact Reachable.left reach inv
    · rw [h]; exact Reachable.right reach inv
  exact ⟨by simpa [childEq] using nodeLookup,
    trie.childGreater node left right route child reach inv hc cl cr childRoute childLink⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.TrieInv.rootBound
#print axioms BoundedTableExperiment.TrieInv.childBound
#print axioms BoundedTableExperiment.candidateFindLeafChild_descent

namespace BoundedTableExperiment

open Flapjack.PanSemStateFiniteExact
open Flapjack

/-- One live-edge step: a reachable parent link moves to a reachable child with
strictly larger route. -/
theorem TrieInv.step {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root : BitVec 64} {keyLen : Nat} (trie : TrieInv s root keyLen)
    {p l r route c : BitVec 64} (reach : Reachable s root p)
    (link : NodeLinkInv s p l r route) (hc : c = l ∨ c = r)
    {cl cr rc : BitVec 64} (childLink : NodeLinkInv s c cl cr rc) :
    Reachable s root c ∧ routeBit route < routeBit rc := by
  have hreach : Reachable s root c := by
    rcases hc with h | h
    · rw [h]; exact Reachable.left reach link
    · rw [h]; exact Reachable.right reach link
  exact ⟨hreach, trie.childGreater p l r route c reach link hc cl cr rc childLink⟩

/-- The child of a live edge inherits the key-length route bound. -/
theorem TrieInv.stepBound {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root : BitVec 64} {keyLen : Nat} (trie : TrieInv s root keyLen)
    {p l r route c : BitVec 64} (reach : Reachable s root p)
    (link : NodeLinkInv s p l r route) (hc : c = l ∨ c = r)
    {cl cr rc : BitVec 64} (childLink : NodeLinkInv s c cl cr rc) :
    routeBit rc < 8 * keyLen := by
  obtain ⟨hreach, _⟩ := trie.step reach link hc childLink
  exact trie.childBound hreach childLink

end BoundedTableExperiment

#print axioms BoundedTableExperiment.TrieInv.step
#print axioms BoundedTableExperiment.TrieInv.stepBound

namespace BoundedTableExperiment

open Flapjack
open Flapjack.PanSemStateFiniteExact

/-- Reverse framing: a post-store node link away from the stored cell is a
pre-store node link. -/
theorem NodeLinkInv.of_store_other {F : Type} {s : PanSemStateFiniteExact 64 F}
    {node left right route watched : BitVec 64} (value : HolWordLab 64)
    (leftSeparate : node ≠ watched) (rightSeparate : node + 8 ≠ watched)
    (routeSeparate : node + 16 ≠ watched)
    {postMem : BitVec 64 → HolWordLab 64}
    (store : @panMemStoresHOL 64 _ watched [value]
      s.memaddrs (Classical.decPred _) s.memory = some postMem)
    (inv : NodeLinkInv { s with memory := postMem } node left right route) :
    NodeLinkInv s node left right route := by
  constructor
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    have frame := actual_one_word_store_frame watched node s.memaddrs
      s.memory value leftSeparate postMem store
    rw [← frame]
    exact inv.leftAt
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    have frame := actual_one_word_store_frame watched (node + 8) s.memaddrs
      s.memory value rightSeparate postMem store
    rw [← frame]
    exact inv.rightAt
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    have frame := actual_one_word_store_frame watched (node + 16) s.memaddrs
      s.memory value routeSeparate postMem store
    rw [← frame]
    exact inv.routeAt

/-- Post-store reachability away from the stored cell is pre-store reachability. -/
theorem Reachable.of_store_other {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root : BitVec 64} {watched : BitVec 64} (value : HolWordLab 64)
    {postMem : BitVec 64 → HolWordLab 64}
    (store : @panMemStoresHOL 64 _ watched [value]
      s.memaddrs (Classical.decPred _) s.memory = some postMem)
    (separate : ∀ p, Reachable s root p →
      p ≠ watched ∧ p + 8 ≠ watched ∧ p + 16 ≠ watched)
    {p : BitVec 64} (reach : Reachable { s with memory := postMem } root p) :
    Reachable s root p := by
  induction reach with
  | root => exact Reachable.root root
  | left reach link ih =>
      obtain ⟨sep0, sep8, sep16⟩ := separate _ ih
      exact Reachable.left ih (link.of_store_other value sep0 sep8 sep16 store)
  | right reach link ih =>
      obtain ⟨sep0, sep8, sep16⟩ := separate _ ih
      exact Reachable.right ih (link.of_store_other value sep0 sep8 sep16 store)

/-- A store outside every reachable node cell preserves the live-edge trie. -/
theorem TrieInv.store_other {F : Type} {s : PanSemStateFiniteExact 64 F}
    {root : BitVec 64} {keyLen : Nat} (trie : TrieInv s root keyLen)
    {watched : BitVec 64} (value : HolWordLab 64)
    {postMem : BitVec 64 → HolWordLab 64}
    (store : @panMemStoresHOL 64 _ watched [value]
      s.memaddrs (Classical.decPred _) s.memory = some postMem)
    (separate : ∀ p, Reachable s root p →
      p ≠ watched ∧ p + 8 ≠ watched ∧ p + 16 ≠ watched) :
    TrieInv { s with memory := postMem } root keyLen := by
  constructor
  · obtain ⟨l, r, route, link⟩ := trie.rootLink
    obtain ⟨sep0, sep8, sep16⟩ := separate root (Reachable.root root)
    exact ⟨l, r, route, link.store_other value sep0 sep8 sep16 store⟩
  · intro p l r route reach link
    have reachOld := Reachable.of_store_other value store separate reach
    obtain ⟨sep0, sep8, sep16⟩ := separate p reachOld
    have linkOld := link.of_store_other value sep0 sep8 sep16 store
    exact trie.routeBound p l r route reachOld linkOld
  · intro p l r route c reach link hc lc rc rcRoute childLink
    have reachOld := Reachable.of_store_other value store separate reach
    obtain ⟨sep0, sep8, sep16⟩ := separate p reachOld
    have linkOld := link.of_store_other value sep0 sep8 sep16 store
    have hreachC : Reachable s root c := by
      rcases hc with h | h
      · rw [h]; exact Reachable.left reachOld linkOld
      · rw [h]; exact Reachable.right reachOld linkOld
    obtain ⟨csep0, csep8, csep16⟩ := separate c hreachC
    have childOld := childLink.of_store_other value csep0 csep8 csep16 store
    exact trie.childGreater p l r route c reachOld linkOld hc lc rc rcRoute childOld

end BoundedTableExperiment

#print axioms BoundedTableExperiment.Reachable.of_store_other
#print axioms BoundedTableExperiment.NodeLinkInv.of_store_other
#print axioms BoundedTableExperiment.TrieInv.store_other
