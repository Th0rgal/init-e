import InitECandidate.Runtime.RlpValidationPushFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A stack push cannot change a word below its newly allocated record. -/
theorem rlpValidation_push_memory_below {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record after stop top payload address : BitVec 64)
    (bounded : record.toNat + 24 ≤ 2^64) (below : address.toNat < record.toNat) :
    (rlpValidationPushPost state record after stop top payload).memory address = state.memory address := by
  have separate : ∀ offset : Nat, offset ≤ 16 → address ≠ record + BitVec.ofNat 64 offset := by
    intro offset small equal
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2^64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have field : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    have same := congrArg BitVec.toNat equal
    rw [field] at same
    omega
  have zero : address ≠ record := by simpa only [BitVec.add_zero] using separate 0 (by decide)
  have eight := separate 8 (by decide)
  have sixteen := separate 16 (by decide)
  simp [rlpValidationPushPost,setVarHOLFinite,sourceWriteWord,zero,eight,sixteen]

#print axioms rlpValidation_push_memory_below
end InitECandidate.Runtime
