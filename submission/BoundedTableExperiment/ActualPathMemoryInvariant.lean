import ActualPathStoreFrame

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact

/-- Concrete address of path slot `i`. -/
def pathAddr (base : BitVec 64) (i : Nat) : BitVec 64 :=
  base + BitVec.ofNat 64 (8 * i)

/-- Actual memory invariant for the recorded path: every slot below `depth`
holds its route word. -/
structure PathMemoryInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (depth : Nat) (routes : Nat → BitVec 64) : Prop where
  routeAt : ∀ i, i < depth → s.memory (pathAddr base i) = .word (routes i)

/-- Pushing one route through an actual one-word `panMemStoresHOL` extends the
path invariant. -/
theorem PathMemoryInv.push {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {depth : Nat} {routes : Nat → BitVec 64}
    (inv : PathMemoryInv s base depth routes)
    (bound : depth < 2 ^ 61)
    (hdom : s.memaddrs (pathAddr base depth))
    {postMem : BitVec 64 → HolWordLab 64} (route : BitVec 64)
    (store : @panMemStoresHOL 64 _ (pathAddr base depth) [.word route]
      s.memaddrs (Classical.decPred _) s.memory = some postMem) :
    PathMemoryInv { s with memory := postMem } base (depth + 1)
      (fun i => if i = depth then route else routes i) := by
  constructor
  intro i hi
  by_cases same : i = depth
  · subst same
    letI : DecidablePred s.memaddrs := Classical.decPred _
    simp only [panMemStoresHOL, panMemStoreHOL_hit _ _ _ _ hdom,
      Option.some.injEq] at store
    subst store
    dsimp only
    change (if pathAddr base i = pathAddr base i then .word route
      else s.memory (pathAddr base i)) = .word (if i = i then route else routes i)
    simp
  · have different : pathAddr base i ≠ pathAddr base depth := by
      intro equal
      unfold pathAddr at equal
      bv_omega
    letI : DecidablePred s.memaddrs := Classical.decPred _
    have frame := actual_one_word_store_frame (pathAddr base depth)
      (pathAddr base i) s.memaddrs s.memory (.word route) different postMem store
    simp only [pathAddr] at frame ⊢
    rw [frame]
    have hroute := inv.routeAt i (by omega)
    simp only [pathAddr] at hroute
    rw [hroute]
    simp [same]

/-- An actual one-word store outside every recorded path slot preserves the
path invariant. -/
theorem PathMemoryInv.store_other {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {depth : Nat} {routes : Nat → BitVec 64}
    (inv : PathMemoryInv s base depth routes)
    {watched : BitVec 64} (value : HolWordLab 64)
    (separate : ∀ i, i < depth → pathAddr base i ≠ watched)
    {postMem : BitVec 64 → HolWordLab 64}
    (store : @panMemStoresHOL 64 _ watched [value]
      s.memaddrs (Classical.decPred _) s.memory = some postMem) :
    PathMemoryInv { s with memory := postMem } base depth routes := by
  constructor
  intro i hi
  letI : DecidablePred s.memaddrs := Classical.decPred _
  have frame := actual_one_word_store_frame watched (pathAddr base i)
    s.memaddrs s.memory value (separate i hi) postMem store
  dsimp only
  rw [frame, inv.routeAt i hi]

/-- The actual path push at `path + depth*8` advances the path invariant by
one slot. This is `PathMemoryInv.push` phrased for the candidate's concrete
store address. -/
theorem PathMemoryInv.push_at {F : Type} {s : PanSemStateFiniteExact 64 F}
    {base : BitVec 64} {depth : Nat} {routes : Nat → BitVec 64}
    (inv : PathMemoryInv s base depth routes)
    (bound : depth < 2 ^ 61)
    (hdom : s.memaddrs (pathAddr base depth))
    {address route : BitVec 64} (haddr : address = pathAddr base depth)
    {postMem : BitVec 64 → HolWordLab 64}
    (store : @panMemStoresHOL 64 _ address [.word route]
      s.memaddrs (Classical.decPred _) s.memory = some postMem) :
    PathMemoryInv { s with memory := postMem } base (depth + 1)
      (fun i => if i = depth then route else routes i) := by
  subst haddr
  exact PathMemoryInv.push inv bound hdom route store

end BoundedTableExperiment

#print axioms BoundedTableExperiment.PathMemoryInv.push
#print axioms BoundedTableExperiment.PathMemoryInv.store_other
#print axioms BoundedTableExperiment.PathMemoryInv.push_at
