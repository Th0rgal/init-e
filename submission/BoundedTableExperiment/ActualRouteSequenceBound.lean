import ActualRouteDepthBound

namespace BoundedTableExperiment

open Flapjack
open Flapjack.PanSemStateFiniteExact

/-- A finite indexed route sequence with strictly increasing decoded indices
below 480.  This is the memory-free core needed to turn an actual descent
sequence into a visit bound. -/
structure RouteSeqInv (depth : Nat) (routes : Nat → BitVec 64) : Prop where
  bounded : ∀ i, i < depth → routeBit (routes i) < 480
  monotone : ∀ i j, i < j → j < depth → routeBit (routes i) < routeBit (routes j)

/-- A strictly increasing route sequence below 480 has at most 480 entries. -/
theorem routeSeq_le_480 {depth : Nat} {routes : Nat → BitVec 64}
    (inv : RouteSeqInv depth routes) : depth ≤ 480 := by
  let f : Fin depth → Nat := fun i => routeBit (routes i)
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
    · have hlt' : routeBit (routes i) < routeBit (routes j) :=
        inv.monotone i.val j.val hlt j.isLt
      exact (Nat.ne_of_lt hlt') hij
    · have hlt' : routeBit (routes j) < routeBit (routes i) :=
        inv.monotone j.val i.val hlt i.isLt
      exact (Nat.ne_of_lt hlt') hij.symm
  have hsub : (Finset.univ.image f) ⊆ Finset.range 480 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact Finset.mem_range.mpr (inv.bounded i i.isLt)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hcard
  simpa using hcard

/-- Concrete linked paths give the memory-free route sequence invariant. -/
theorem LinkedPathInv.toRouteSeq {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {depth : Nat} {routes : Nat → BitVec 64}
    {nodes left right : Nat → BitVec 64}
    (inv : LinkedPathInv s base depth routes nodes left right) :
    RouteSeqInv depth routes :=
  ⟨inv.bounded, inv.monotone⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.routeSeq_le_480
#print axioms BoundedTableExperiment.LinkedPathInv.toRouteSeq
