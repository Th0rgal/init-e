import InitECandidate.Runtime.ScratchAllocationSource
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack

/-- Rounding the descending allocation end down never consumes less than
the requested size, provided subtraction does not wrap. -/
theorem scratchAllocationEnd_before (pointer size : BitVec 64)
    (fits : size.toNat ≤ pointer.toNat) :
    (scratchAllocationEnd pointer size).toNat + size.toNat ≤ pointer.toNat := by
  have masked : (scratchAllocationEnd pointer size).toNat ≤ (pointer - size).toNat := by
    unfold scratchAllocationEnd
    rw [BitVec.toNat_and]
    exact Nat.and_le_left
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr fits)] at masked
  omega

/-- Every field of the 88-byte parser record lies below the old scratch
frontier, with the source pointer addition interpreted without wrap. -/
theorem scratchRecord_field_nat (scratch : BitVec 64) (field : Nat)
    (fits : 88 ≤ scratch.toNat) (inside : field < 88) :
    (scratchAllocationEnd scratch 88 + BitVec.ofNat 64 field).toNat =
      (scratchAllocationEnd scratch 88).toNat + field ∧
    (scratchAllocationEnd scratch 88 + BitVec.ofNat 64 field).toNat < scratch.toNat := by
  have before := scratchAllocationEnd_before scratch 88 fits
  have small : field < 2^64 := by omega
  have noWrap : (scratchAllocationEnd scratch 88).toNat + (BitVec.ofNat 64 field).toNat < 2^64 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    have top := scratch.isLt
    change scratch.toNat < 2^64 at top
    change (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat at before
    omega
  rw [BitVec.toNat_add_of_lt noWrap,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  exact ⟨rfl,by change (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat at before; omega⟩

/-- An aligned heap path above the old scratch frontier cannot share a
containing word with any newly allocated parser record field. -/
theorem scratchRecord_path_separate (scratch nibs count : BitVec 64)
    (fits : 88 ≤ scratch.toNat) (below : scratch.toNat ≤ nibs.toNat)
    (aligned : nibs.toNat % 8 = 0) (bounded : nibs.toNat + count.toNat ≤ 2^64) :
    ∀ offset : Nat, offset < count.toNat → ∀ field : Nat, field < 88 →
      panByteAlignHOL (nibs + BitVec.ofNat 64 offset) ≠ scratchAllocationEnd scratch 88 + BitVec.ofNat 64 field := by
  intro offset inside field inRecord equal
  have fieldBound := (scratchRecord_field_nat scratch field fits inRecord).2
  have small : offset < 2^64 := by have top := count.isLt; omega
  have indexBound : (BitVec.ofNat 64 offset).toNat < count.toNat := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    exact inside
  have pathBound := (hashOccupancy_aligned_interval nibs count (BitVec.ofNat 64 offset) aligned bounded indexBound).1
  have same := congrArg BitVec.toNat equal
  omega

#print axioms scratchAllocationEnd_before
#print axioms scratchRecord_field_nat
#print axioms scratchRecord_path_separate
end InitECandidate.Runtime
