import ActualWordSepFrame
import ReachableOrderInvariant

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.PanSemStateFiniteExact

set_option maxHeartbeats 1000000

/-- Every cell of an internal node record in the pointer slab lies strictly
below the end of the slab, hence below a fresh path buffer placed after it. -/
theorem slab_node_cells_below (base cap path : Nat)
    (pathEq : path = base + 24 * (cap / 2))
    {p : Nat} (hp : p ∈ slab base cap) :
    p < path ∧ p + 8 < path ∧ p + 16 < path := by
  obtain ⟨i, hi, rfl⟩ := (slab_mem (base := base) (cap := cap) (x := p)).mp hp
  refine ⟨by omega, by omega, by omega⟩

/-- If every tagged node pointer is a member of the node slab and the path
buffer starts at the slab end, every tagged node cell is below the path. -/
theorem taggedNodeCells_below_of_slab {F : Type}
    {s : PanSemStateFiniteExact 64 F} {root cap : BitVec 64}
    {base capN path : Nat}
    (hmem : ∀ p, ReachableInternal s cap root p → p.toNat ∈ slab base capN)
    (pathEq : path = base + 24 * (capN / 2)) (hpath : path ≤ 2 ^ 64) :
    ∀ b, b ∈ taggedNodeCells s cap root → b.toNat < path := by
  intro b hb
  obtain ⟨p, reach, hc⟩ := hb
  rcases hc with h | h | h
  · rw [h]
    exact (slab_node_cells_below base capN path pathEq (hmem p reach)).1
  · rw [h]
    have h16 := (slab_node_cells_below base capN path pathEq (hmem p reach)).2.2
    have h8 : (p + 8).toNat = p.toNat + 8 := by
      rw [BitVec.toNat_add]
      change (p.toNat + BitVec.toNat (8#64)) % 2 ^ 64 = p.toNat + 8
      have hb8 : BitVec.toNat (8#64) = 8 := by decide
      rw [hb8]
      rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [h]
    have h16 := (slab_node_cells_below base capN path pathEq (hmem p reach)).2.2
    have h16' : (p + 16).toNat = p.toNat + 16 := by
      rw [BitVec.toNat_add]
      change (p.toNat + BitVec.toNat (16#64)) % 2 ^ 64 = p.toNat + 16
      have hb16 : BitVec.toNat (16#64) = 16 := by decide
      rw [hb16]
      rw [Nat.mod_eq_of_lt (by omega)]
    omega

end BoundedTableExperiment

#print axioms BoundedTableExperiment.slab_node_cells_below
#print axioms BoundedTableExperiment.taggedNodeCells_below_of_slab
