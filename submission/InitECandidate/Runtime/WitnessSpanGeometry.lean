import InitECandidate.Runtime.WitnessArrayLinked
namespace InitECandidate.Runtime

/-- Accepted witness offsets partition the original input without wrapping.
Every list span is bounded by the full input length, for database hash costs. -/
theorem witness_span_geometry (P L OW middle last : BitVec 64)
    (fits : P.toNat + L.toNat < 2^64) (inside : OW.toNat ≤ L.toNat)
    (lower : 12 ≤ middle.toNat) (ordered : middle.toNat ≤ last.toNat)
    (lastBound : last.toNat ≤ (L - OW).toNat) :
    (middle - (12#64)).toNat ≤ L.toNat ∧ (last - middle).toNat ≤ L.toNat ∧
    ((L - OW) - last).toNat ≤ L.toNat ∧
    ((P + OW) + (12#64)).toNat + (middle - (12#64)).toNat ≤ P.toNat + L.toNat ∧
    ((P + OW) + middle).toNat + (last - middle).toNat ≤ P.toNat + L.toNat ∧
    ((P + OW) + last).toNat + ((L - OW) - last).toNat = P.toNat + L.toNat := by
  have lenEq : (L - OW).toNat = L.toNat - OW.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact inside)
  have firstEq : (middle - (12#64)).toNat = middle.toNat - 12 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact lower)]; rfl
  have secondEq : (last - middle).toNat = last.toNat - middle.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact ordered)
  have thirdEq : ((L - OW) - last).toNat = L.toNat - OW.toNat - last.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact lastBound),lenEq]
  have start : (P + OW).toNat = P.toNat + OW.toNat := by
    rw [BitVec.toNat_add_of_lt (by omega)]
  have start12 : ((P + OW) + (12#64)).toNat = P.toNat + OW.toNat + 12 := by
    rw [BitVec.toNat_add_of_lt (by rw [start]; change P.toNat + OW.toNat + 12 < 2^64; omega),start]; rfl
  have startMiddle : ((P + OW) + middle).toNat = P.toNat + OW.toNat + middle.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [start]; omega),start]
  have startLast : ((P + OW) + last).toNat = P.toNat + OW.toNat + last.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [start]; omega),start]
  rw [firstEq,secondEq,thirdEq,start12,startMiddle,startLast]
  omega

#print axioms witness_span_geometry
end InitECandidate.Runtime
