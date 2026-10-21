import ActualPathMemoryInvariant
import ActualLinkMemoryInvariant

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact

/-- Decode the candidate's monotone route word into its bit index:
`byteOffset*256 + (255 - mask)` becomes `8*byteOffset + inverseMaskBit`. -/
def routeBit (route : BitVec 64) : Nat :=
  8 * (route >>> 8).toNat + (route &&& 255).toNat

/-- Concrete route-order invariant over the actual path words in memory: every
recorded route decodes to a bit index below 480 and route indices strictly
increase along the recorded path. -/
structure RouteOrderInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (depth : Nat) (routes : Nat → BitVec 64) : Prop where
  memory : PathMemoryInv s base depth routes
  bounded : ∀ i, i < depth → routeBit (routes i) < 480
  monotone : ∀ i j, i < j → j < depth → routeBit (routes i) < routeBit (routes j)

/-- A strictly increasing sequence of route indices below 480 has at most 480
recorded visits. -/
theorem routeDepth_le_480 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {depth : Nat} {routes : Nat → BitVec 64}
    (inv : RouteOrderInv s base depth routes) : depth ≤ 480 := by
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

/-- Pushing a route with a larger decoded index preserves route order and
extends the depth bound by one. -/
theorem RouteOrderInv.push {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {depth : Nat} {routes : Nat → BitVec 64}
    (inv : RouteOrderInv s base depth routes)
    (bound : depth < 2 ^ 61)
    (hdom : s.memaddrs (pathAddr base depth))
    {postMem : BitVec 64 → HolWordLab 64} (route : BitVec 64)
    (store : @panMemStoresHOL 64 _ (pathAddr base depth) [.word route]
      s.memaddrs (Classical.decPred _) s.memory = some postMem)
    (last : ∀ i, i < depth → routeBit (routes i) < routeBit route)
    (routeBound : routeBit route < 480) :
    RouteOrderInv { s with memory := postMem } base (depth + 1)
      (fun i => if i = depth then route else routes i) := by
  refine ⟨PathMemoryInv.push inv.memory bound hdom route store, ?_, ?_⟩
  · intro i hi
    by_cases same : i = depth
    · subst same; simp [routeBound]
    · simp [same]; exact inv.bounded i (by omega)
  · intro i j hij hj
    by_cases jd : j = depth
    · have hjeq : j = depth := jd
      have hi_ne : i ≠ depth := by omega
      have : (if i = depth then route else routes i) = routes i := by simp [hi_ne]
      simp [this, hjeq]
      exact last i (by omega)
    · have hjd : j < depth := by omega
      have hi' : i < depth := by omega
      have hiEq : (if i = depth then route else routes i) = routes i := by simp [show i ≠ depth by omega]
      have hjEq : (if j = depth then route else routes j) = routes j := by simp [jd]
      simp [hiEq, hjEq]
      exact inv.monotone i j hij hjd

end BoundedTableExperiment

#print axioms BoundedTableExperiment.routeDepth_le_480
#print axioms BoundedTableExperiment.RouteOrderInv.push

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact

/-- Path invariant tied to concrete 24-byte node links: each recorded path slot
holds the route of a node whose `NodeLinkInv` (actual left/right/route memory
words) is present. -/
structure LinkedPathInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (depth : Nat) (routes : Nat → BitVec 64)
    (nodes left right : Nat → BitVec 64) : Prop where
  memory : PathMemoryInv s base depth routes
  links : ∀ i, i < depth → NodeLinkInv s (nodes i) (left i) (right i) (routes i)
  bounded : ∀ i, i < depth → routeBit (routes i) < 480
  monotone : ∀ i j, i < j → j < depth → routeBit (routes i) < routeBit (routes j)

/-- Concrete node links give the route-order invariant used for the visit
bound. -/
theorem LinkedPathInv.toRouteOrder {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {depth : Nat} {routes : Nat → BitVec 64}
    {nodes left right : Nat → BitVec 64}
    (inv : LinkedPathInv s base depth routes nodes left right) :
    RouteOrderInv s base depth routes :=
  ⟨inv.memory, inv.bounded, inv.monotone⟩

/-- Actual linked path depth is at most 480. -/
theorem LinkedPathInv.depth_le_480 {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {depth : Nat} {routes : Nat → BitVec 64}
    {nodes left right : Nat → BitVec 64}
    (inv : LinkedPathInv s base depth routes nodes left right) : depth ≤ 480 :=
  routeDepth_le_480 inv.toRouteOrder

end BoundedTableExperiment

#print axioms BoundedTableExperiment.LinkedPathInv.toRouteOrder
#print axioms BoundedTableExperiment.LinkedPathInv.depth_le_480
