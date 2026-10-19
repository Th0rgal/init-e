import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack

/-- Subranges of an aligned buffer need not themselves start at aligned
addresses. Stores in them still cannot affect words outside the outer buffer. -/
theorem aligned_subinterval_memory_separate (base size shift count watched : BitVec 64)
    (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + size.toNat ≤ 33806089496)
    (inside : shift.toNat + count.toNat ≤ size.toNat)
    (outside : watched.toNat < base.toNat ∨ base.toNat + size.toNat ≤ watched.toNat) :
    (base + shift).toNat + count.toNat ≤ 33806089496 ∧
      ∀ offset : Nat, offset < count.toNat →
        watched ≠ (base + shift) + BitVec.ofNat 64 offset ∧
        watched ≠ panByteAlignHOL ((base + shift) + BitVec.ofNat 64 offset) := by
  have natural : (base + shift).toNat = base.toNat + shift.toNat :=
    BitVec.toNat_add_of_lt (by omega)
  refine ⟨by rw [natural]; omega,?_⟩
  intro offset below
  have shiftWord : BitVec.ofNat 64 shift.toNat = shift := by simp
  have address : (base + shift) + BitVec.ofNat 64 offset =
      base + BitVec.ofNat 64 (shift.toNat + offset) := by
    rw [BitVec.ofNat_add,shiftWord,BitVec.add_assoc]
  rw [address]
  exact memcpy_interval_separate base size watched aligned bounded outside (shift.toNat + offset) (by omega)

#print axioms aligned_subinterval_memory_separate
end InitECandidate.Runtime
