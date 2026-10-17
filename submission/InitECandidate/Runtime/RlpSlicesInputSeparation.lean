import InitECandidate.Runtime.RlpSliceAddressSeparation
import InitECandidate.Runtime.AllocationSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- An aligned input interval before the slice allocation is separate from
both destination words of every allocated slice entry. -/
theorem rlpSlices_input_cells_separate (input length array index count : BitVec 64)
    (inputAligned : input.toNat % 8 = 0)
    (inputBefore : input.toNat + length.toNat ≤ array.toNat)
    (inside : index.toNat < count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (offset : Nat) (offsetInside : offset < length.toNat) :
    panByteAlignHOL (input + BitVec.ofNat 64 offset) ≠ array + index * 16#64 ∧
    panByteAlignHOL (input + BitVec.ofNat 64 offset) ≠ array + index * 16#64 + 8#64 := by
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2^64 = offset
    exact Nat.mod_eq_of_lt (Nat.lt_trans offsetInside length.isLt)
  have interval := hashOccupancy_aligned_interval input length (BitVec.ofNat 64 offset) inputAligned
    (by omega) (by rw [offsetNat]; exact offsetInside)
  have cell0 := rlpSlice_cell_toNat array index count 0 inside (by decide) fits
  simp only [BitVec.add_zero,Nat.add_zero] at cell0
  have cell8 := rlpSlice_cell_toNat array index count 8 inside (by decide) fits
  constructor
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [cell0] at same
    omega
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [cell8] at same
    omega

#print axioms rlpSlices_input_cells_separate
end InitECandidate.Runtime
