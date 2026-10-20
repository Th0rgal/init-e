import InitECandidate.Runtime.WitnessArrayOuter
namespace InitECandidate.Runtime

theorem witness_blob_span_geometry (length offset middle last : BitVec 64)
    (small : length.toNat≤134217712) (long : 2≤length.toNat)
    (inside : offset.toNat≤length.toNat-2) (lower : 12≤middle.toNat)
    (ordered : middle.toNat≤last.toNat)
    (lastBound : last.toNat≤((length-2)-offset).toNat) :
    (2713731432≤(((2713731432 : BitVec 64)+2+offset)+12).toNat ∧
      (((2713731432 : BitVec 64)+2+offset)+12).toNat+(middle-12).toNat≤2713731432+length.toNat) ∧
    (2713731432≤(((2713731432 : BitVec 64)+2+offset)+middle).toNat ∧
      (((2713731432 : BitVec 64)+2+offset)+middle).toNat+(last-middle).toNat≤2713731432+length.toNat) ∧
    (2713731432≤(((2713731432 : BitVec 64)+2+offset)+last).toNat ∧
      (((2713731432 : BitVec 64)+2+offset)+last).toNat+(((length-2)-offset)-last).toNat≤2713731432+length.toNat) := by
  have two : (2 : BitVec 64).toNat=2 := rfl
  have twelve : (12 : BitVec 64).toNat=12 := rfl
  have len : (length-2).toNat=length.toNat-2 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [two]; exact long)),two]
  have remaining : ((length-2)-offset).toNat=length.toNat-2-offset.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [len]; exact inside)),len]
  rw [remaining] at lastBound
  have start : ((2713731432 : BitVec 64)+2+offset).toNat=2713731434+offset.toNat := by
    change ((2713731434 : BitVec 64)+offset).toNat=_
    rw [BitVec.toNat_add_of_lt (by change 2713731434+offset.toNat<2^64; omega)]
    rfl
  have firstStart : (((2713731432 : BitVec 64)+2+offset)+12).toNat=2713731434+offset.toNat+12 := by
    rw [BitVec.toNat_add_of_lt (by rw [start,twelve]; omega),start,twelve]
  have middleStart : (((2713731432 : BitVec 64)+2+offset)+middle).toNat=2713731434+offset.toNat+middle.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [start]; omega),start]
  have lastStart : (((2713731432 : BitVec 64)+2+offset)+last).toNat=2713731434+offset.toNat+last.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [start]; omega),start]
  have firstLength : (middle-12).toNat=middle.toNat-12 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [twelve]; exact lower)),twelve]
  have middleLength : (last-middle).toNat=last.toNat-middle.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr ordered)
  have lastLength : (((length-2)-offset)-last).toNat=length.toNat-2-offset.toNat-last.toNat := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [remaining]; exact lastBound)),remaining]
  rw [firstStart,middleStart,lastStart,firstLength,middleLength,lastLength]
  omega

#print axioms witness_blob_span_geometry
end InitECandidate.Runtime
