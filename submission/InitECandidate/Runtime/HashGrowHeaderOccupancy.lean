import InitECandidate.Runtime.HashGrowHeader
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Installing growth's new header pointers does not change its separately
allocated occupancy bytes. -/
theorem htabGrow_header_preserves_occupancy {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity keys values used order orderPos : BitVec 64)
    (aligned : used.toNat % 8 = 0) (headerBefore : table.toNat + 72 ≤ used.toNat)
    (bounded : used.toNat + capacity.toNat ≤ 33806089496) :
    hashOccupiedCount capacity (hashOccupancyRead
      (htabGrowHeaderPost state table capacity keys values used order orderPos) used) =
      hashOccupiedCount capacity (hashOccupancyRead state used) := by
  have separate : ∀ offset : Nat, offset ≤ 64 → ∀ index : BitVec 64, index.toNat < capacity.toNat →
      panByteAlignHOL (used + index) ≠ table + BitVec.ofNat 64 offset := by
    intro offset small
    apply hashOccupancy_separate_allocation used capacity _ aligned (by omega)
    left
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    omega
  unfold htabGrowHeaderPost
  rw [sourceWriteWord_occupancy_preserved _ capacity used (table + 24) 0 (separate 24 (by decide))]
  rw [sourceWriteWord_occupancy_preserved _ capacity used (table + 64) orderPos (separate 64 (by decide))]
  rw [sourceWriteWord_occupancy_preserved _ capacity used (table + 56) order (separate 56 (by decide))]
  rw [sourceWriteWord_occupancy_preserved _ capacity used (table + 48) used (separate 48 (by decide))]
  rw [sourceWriteWord_occupancy_preserved _ capacity used (table + 40) values (separate 40 (by decide))]
  rw [sourceWriteWord_occupancy_preserved _ capacity used (table + 32) keys (separate 32 (by decide))]
  rw [sourceWriteWord_occupancy_preserved _ capacity used (table + 16) capacity (separate 16 (by decide))]

#print axioms htabGrow_header_preserves_occupancy
end InitECandidate.Runtime
