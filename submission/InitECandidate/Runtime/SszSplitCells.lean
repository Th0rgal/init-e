import InitECandidate.Runtime.SszSplitVarListStepMain
namespace InitECandidate.Runtime

theorem sszCell_toNat (x : BitVec 64) (hx : x.toNat < 2 ^ 60) : (x * 16).toNat = x.toNat * 16 := by
  rw [BitVec.toNat_mul]; simp; omega

theorem sszCell_toNat8 (x : BitVec 64) (hx : x.toNat < 2 ^ 60) : (x * 16 + 8).toNat = x.toNat * 16 + 8 := by
  rw [BitVec.toNat_add, sszCell_toNat x hx]; simp; omega

theorem sszCell_len_ne_ptr (arr x y : BitVec 64) (hx : x.toNat < 2 ^ 60) (hy : y.toNat < 2 ^ 60) :
    arr + x * 16 + 8 ≠ arr + y * 16 := by
  intro h
  rw [BitVec.add_assoc, BitVec.add_right_inj] at h
  have := congrArg BitVec.toNat h
  rw [sszCell_toNat8 x hx, sszCell_toNat y hy] at this
  omega

theorem sszCell_ptr_ne (arr x y : BitVec 64) (hx : x.toNat < 2 ^ 60) (hy : y.toNat < 2 ^ 60) (ne : x ≠ y) :
    arr + x * 16 ≠ arr + y * 16 := by
  intro h
  rw [BitVec.add_right_inj] at h
  have := congrArg BitVec.toNat h
  rw [sszCell_toNat x hx, sszCell_toNat y hy] at this
  exact ne (BitVec.eq_of_toNat_eq (by omega))

theorem sszCell_len_ne (arr x y : BitVec 64) (hx : x.toNat < 2 ^ 60) (hy : y.toNat < 2 ^ 60) (ne : x ≠ y) :
    arr + x * 16 + 8 ≠ arr + y * 16 + 8 := by
  intro h
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_right_inj] at h
  have := congrArg BitVec.toNat h
  rw [sszCell_toNat8 x hx, sszCell_toNat8 y hy] at this
  exact ne (BitVec.eq_of_toNat_eq (by omega))

#print axioms sszCell_len_ne
end InitECandidate.Runtime
