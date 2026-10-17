import InitECandidate.Runtime.TxFixedBytesArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Slice-cell addresses do not wrap within a bounded allocated array. -/
theorem rlpSlice_cell_toNat (array index count : BitVec 64) (offset : Nat)
    (inside : index.toNat < count.toNat) (offsetBound : offset ≤ 8)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64) :
    (array + index * 16#64 + BitVec.ofNat 64 offset).toNat = array.toNat + index.toNat * 16 + offset := by
  have product : (index * 16#64).toNat = index.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change index.toNat * 16 < 2^64; omega)]
    rfl
  have start : (array + index * 16#64).toNat = array.toNat + index.toNat * 16 := by
    rw [BitVec.toNat_add_of_lt (by rw [product]; omega),product]
  have small : (BitVec.ofNat 64 offset).toNat = offset := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add_of_lt (by rw [start,small]; omega),start,small]

/-- Neither word of an earlier entry aliases either word of a later entry. -/
theorem rlpSlice_cells_separate (array earlier later count : BitVec 64) (left right : Nat)
    (ordered : earlier.toNat < later.toNat) (inside : later.toNat < count.toNat)
    (leftBound : left ≤ 8) (rightBound : right ≤ 8)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64) :
    array + earlier * 16#64 + BitVec.ofNat 64 left ≠ array + later * 16#64 + BitVec.ofNat 64 right := by
  intro same
  have equal := congrArg BitVec.toNat same
  rw [rlpSlice_cell_toNat array earlier count left (by omega) leftBound fits,
    rlpSlice_cell_toNat array later count right inside rightBound fits] at equal
  omega

#print axioms rlpSlice_cell_toNat
#print axioms rlpSlice_cells_separate
end InitECandidate.Runtime
