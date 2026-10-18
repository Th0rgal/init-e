import InitECandidate.Runtime.BlobHashesBodyBound
namespace InitECandidate.Runtime

theorem blobHashesBodyCost_mono {first second : Nat} (bounded : first ≤ second) :
    blobHashesBodyCost first ≤ blobHashesBodyCost second := by
  have factor : (2 * first + 1) * 15 + 19 ≤ (2 * second + 1) * 15 + 19 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right 15 (Nat.add_le_add_right (Nat.mul_le_mul_left 2 bounded) 1)) 19
  have quadratic := Nat.mul_le_mul bounded factor
  have copies := Nat.mul_le_mul bounded (Nat.add_le_add_right quadratic 92651)
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add quadratic (Nat.mul_le_mul_right 12 bounded)) 4)
    (Nat.add_le_add_right copies 2)

#print axioms blobHashesBodyCost_mono
end InitECandidate.Runtime
