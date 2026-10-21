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
