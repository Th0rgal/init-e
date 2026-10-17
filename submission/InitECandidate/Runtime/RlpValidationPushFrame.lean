import InitECandidate.Runtime.RlpValidationPushExecution
import InitECandidate.Runtime.ScratchAllocationFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A new validator stack record preserves every memory word at or above
the previous scratch frontier, including all older continuation records. -/
theorem rlpValidation_push_memory_above {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch after stop top payload address : BitVec 64)
    (fits : 24 ≤ scratch.toNat) (above : scratch.toNat ≤ address.toNat) :
    (rlpValidationPushPost state (scratchAllocationEnd scratch 24) after stop top payload).memory address =
      state.memory address := by
  have field0 := (scratchAllocation_field_nat scratch 24 0 fits (by decide)).2
  have field8 := (scratchAllocation_field_nat scratch 24 8 fits (by decide)).2
  have field16 := (scratchAllocation_field_nat scratch 24 16 fits (by decide)).2
  have separate0 : address ≠ scratchAllocationEnd scratch 24 := by
    intro equal
    have same := congrArg BitVec.toNat equal
    change (scratchAllocationEnd scratch 24 + 0#64).toNat < scratch.toNat at field0
    rw [BitVec.add_zero] at field0
    omega
  have separate8 : address ≠ scratchAllocationEnd scratch 24 + 8 := by
    intro equal
    have same := congrArg BitVec.toNat equal
    change (scratchAllocationEnd scratch 24 + 8).toNat < scratch.toNat at field8
    omega
  have separate16 : address ≠ scratchAllocationEnd scratch 24 + 16 := by
    intro equal
    have same := congrArg BitVec.toNat equal
    change (scratchAllocationEnd scratch 24 + 16).toNat < scratch.toNat at field16
    omega
  change address ≠ scratchAllocationEnd scratch 24#64 at separate0
  change address ≠ scratchAllocationEnd scratch 24#64 + 8#64 at separate8
  change address ≠ scratchAllocationEnd scratch 24#64 + 16#64 at separate16
  simp [rlpValidationPushPost,setVarHOLFinite,sourceWriteWord,separate0,separate8,separate16]

/-- Every field of an older 24-byte continuation record is preserved by a
new push below the scratch frontier, without a per-field separation premise. -/
theorem rlpValidation_push_preserves_older_record {F : Type} (state : PanSemStateFiniteExact 64 F)
    (scratch after stop top payload older : BitVec 64)
    (fits : 24 ≤ scratch.toNat) (above : scratch.toNat ≤ older.toNat)
    (bounded : older.toNat + 24 ≤ 2^64) :
    ∀ field : Nat, field < 24 →
      (rlpValidationPushPost state (scratchAllocationEnd scratch 24) after stop top payload).memory
        (older + BitVec.ofNat 64 field) = state.memory (older + BitVec.ofNat 64 field) := by
  intro field inside
  have small : field < 2^64 := by omega
  have addressNat : (older + BitVec.ofNat 64 field).toNat = older.toNat + field := by
    rw [BitVec.toNat_add_of_lt (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]; omega),
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  apply rlpValidation_push_memory_above state scratch after stop top payload _ fits
  rw [addressNat]
  omega

#print axioms rlpValidation_push_preserves_older_record
#print axioms rlpValidation_push_memory_above
end InitECandidate.Runtime
