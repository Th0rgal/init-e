import ActualPathStoreFrame

namespace BoundedTableExperiment

open InitECandidate.Runtime
open Flapjack
open Flapjack.PanSemStateFiniteExact

/-- Actual memory invariant for one 24-byte Patricia internal node. -/
structure NodeLinkInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (node : BitVec 64) (left right route : BitVec 64) : Prop where
  leftAt : s.memory node = .word left
  rightAt : s.memory (node + 8) = .word right
  routeAt : s.memory (node + 16) = .word route

/-- An actual one-word store of the left child preserves the right child and
route of the node. -/
theorem NodeLinkInv.setLeft {F : Type} {s : PanSemStateFiniteExact 64 F}
    {node left right route : BitVec 64} (inv : NodeLinkInv s node left right route)
    (hdom : s.memaddrs node)
    {postMem : BitVec 64 → HolWordLab 64} (newLeft : BitVec 64)
    (store : @panMemStoresHOL 64 _ node [.word newLeft]
      s.memaddrs (Classical.decPred _) s.memory = some postMem) :
    NodeLinkInv { s with memory := postMem } node newLeft right route := by
  constructor
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    simp only [panMemStoresHOL, panMemStoreHOL_hit _ _ _ _ hdom,
      Option.some.injEq] at store
    subst store
    dsimp only
    simp
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    have different : node + 8 ≠ node := by bv_omega
    have frame := actual_one_word_store_frame node (node + 8) s.memaddrs
      s.memory (.word newLeft) different postMem store
    dsimp only
    rw [frame, inv.rightAt]
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    have different : node + 16 ≠ node := by bv_omega
    have frame := actual_one_word_store_frame node (node + 16) s.memaddrs
      s.memory (.word newLeft) different postMem store
    dsimp only
    rw [frame, inv.routeAt]

/-- An actual one-word store of the right child preserves the left child and
route of the node. -/
theorem NodeLinkInv.setRight {F : Type} {s : PanSemStateFiniteExact 64 F}
    {node left right route : BitVec 64} (inv : NodeLinkInv s node left right route)
    (hdom : s.memaddrs (node + 8))
    {postMem : BitVec 64 → HolWordLab 64} (newRight : BitVec 64)
    (store : @panMemStoresHOL 64 _ (node + 8) [.word newRight]
      s.memaddrs (Classical.decPred _) s.memory = some postMem) :
    NodeLinkInv { s with memory := postMem } node left newRight route := by
  constructor
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    have different : node ≠ node + 8 := by bv_omega
    have frame := actual_one_word_store_frame (node + 8) node s.memaddrs
      s.memory (.word newRight) different postMem store
    dsimp only
    rw [frame, inv.leftAt]
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    simp only [panMemStoresHOL, panMemStoreHOL_hit _ _ _ _ hdom,
      Option.some.injEq] at store
    subst store
    dsimp only
    simp
  · letI : DecidablePred s.memaddrs := Classical.decPred _
    have different : node + 16 ≠ node + 8 := by bv_omega
    have frame := actual_one_word_store_frame (node + 8) (node + 16) s.memaddrs
      s.memory (.word newRight) different postMem store
    dsimp only
    rw [frame, inv.routeAt]

end BoundedTableExperiment

#print axioms BoundedTableExperiment.NodeLinkInv.setLeft
#print axioms BoundedTableExperiment.NodeLinkInv.setRight
