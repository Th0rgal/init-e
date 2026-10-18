import InitECandidate.Runtime.AuthorizationsInnerSlicesBound
namespace InitECandidate.Runtime

theorem authorizationInnerSlicesCost_mono_left (left right inputLength : Nat)
    (bounded : left ≤ right) :
    authorizationInnerSlicesCost left inputLength ≤ authorizationInnerSlicesCost right inputLength := by
  have factor : (2 * left + 1) * 15 + 19 ≤ (2 * right + 1) * 15 + 19 := by omega
  have work := Nat.mul_le_mul bounded factor
  have bytes := Nat.mul_le_mul_right 12 bounded
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add work bytes) 4) _

/-- A nested input span cannot cost more than the common whole-input budget. -/
theorem authorizationInnerSlicesCost_within_input
    (pointer length input inputLength : BitVec 64)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat) :
    authorizationInnerSlicesCost length.toNat inputLength.toNat ≤
      authorizationInnerSlicesCost inputLength.toNat inputLength.toNat :=
  authorizationInnerSlicesCost_mono_left _ _ _ (by omega)

#print axioms authorizationInnerSlicesCost_mono_left
#print axioms authorizationInnerSlicesCost_within_input
end InitECandidate.Runtime
