import InitECandidate.Runtime.SourceByteStore
namespace InitECandidate.Runtime
open Flapjack

/-- Exact 64-bit byte alignment rounds down to an eight-byte boundary. -/
theorem panByteAlign_toNat64 (address : BitVec 64) :
    (panByteAlignHOL address).toNat = address.toNat / 8 * 8 := by
  have bound : address.toNat / 8 * 8 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) address.isLt
  simpa [panByteAlignHOL,BitVec.toNat_ofNat] using Nat.mod_eq_of_lt bound

/-- An aligned byte-array allocation stays within its natural interval even
when a slot load rounds its address down to an aligned word. -/
theorem hashOccupancy_aligned_interval (used capacity index : BitVec 64)
    (aligned : used.toNat % 8 = 0)
    (bounded : used.toNat + capacity.toNat ≤ 2 ^ 64)
    (inside : index.toNat < capacity.toNat) :
    used.toNat ≤ (panByteAlignHOL (used + index)).toNat ∧
      (panByteAlignHOL (used + index)).toNat < used.toNat + capacity.toNat := by
  have noWrap : used.toNat + index.toNat < 2 ^ 64 := by omega
  rw [panByteAlign_toNat64,BitVec.toNat_add_of_lt noWrap]
  have original := Nat.mod_add_div used.toNat 8
  have current := Nat.mod_add_div (used.toNat + index.toNat) 8
  have remainder := Nat.mod_lt (used.toNat + index.toNat) (by decide : 0 < 8)
  omega

/-- Natural disjoint allocation intervals discharge the aligned-cell
separation premise used by the occupancy-preservation proofs. -/
theorem hashOccupancy_separate_allocation (used capacity destination : BitVec 64)
    (aligned : used.toNat % 8 = 0)
    (bounded : used.toNat + capacity.toNat ≤ 2 ^ 64)
    (outside : destination.toNat < used.toNat ∨ used.toNat + capacity.toNat ≤ destination.toNat) :
    ∀ index : BitVec 64, index.toNat < capacity.toNat →
      panByteAlignHOL (used + index) ≠ destination := by
  intro index inside same
  have interval := hashOccupancy_aligned_interval used capacity index aligned bounded inside
  have equal := congrArg BitVec.toNat same
  omega

/-- Allocation guards cap source table sizes far below the 64-bit arithmetic
threshold required by the growth and count proofs. -/
theorem heap_allocation_small (used capacity : BitVec 64)
    (bounded : used.toNat + capacity.toNat ≤ 33806089496) :
    capacity.toNat + 1 < 2 ^ 63 ∧ used.toNat + capacity.toNat ≤ 2 ^ 64 := by omega

#print axioms panByteAlign_toNat64
#print axioms hashOccupancy_aligned_interval
#print axioms hashOccupancy_separate_allocation
#print axioms heap_allocation_small
end InitECandidate.Runtime
