import InitECandidate.Runtime.HashGrowHeaderState
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Growth's header installation preserves every old array word beyond the
header, independently of the newly installed pointer values. -/
theorem htabGrowHeaderPost_earlier {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity keys values used order orderPos watched : BitVec 64)
    (afterHeader : table.toNat + 72 ≤ watched.toNat) :
    (htabGrowHeaderPost state table capacity keys values used order orderPos).memory watched = state.memory watched := by
  have separate : ∀ offset : Nat, offset ≤ 64 → watched ≠ table + BitVec.ofNat 64 offset := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; have := watched.isLt; omega),natural]
    intro same
    have equal := congrArg BitVec.toNat same
    rw [address] at equal
    omega
  have s24 : watched ≠ table + (24 : BitVec 64) := separate 24 (by decide)
  have s64 : watched ≠ table + (64 : BitVec 64) := separate 64 (by decide)
  have s56 : watched ≠ table + (56 : BitVec 64) := separate 56 (by decide)
  have s48 : watched ≠ table + (48 : BitVec 64) := separate 48 (by decide)
  have s40 : watched ≠ table + (40 : BitVec 64) := separate 40 (by decide)
  have s32 : watched ≠ table + (32 : BitVec 64) := separate 32 (by decide)
  have s16 : watched ≠ table + (16 : BitVec 64) := separate 16 (by decide)
  simp only [htabGrowHeaderPost,sourceWriteWord]
  rw [if_neg s24,if_neg s64,if_neg s56,if_neg s48,if_neg s40,if_neg s32,if_neg s16]

#print axioms htabGrowHeaderPost_earlier
end InitECandidate.Runtime
