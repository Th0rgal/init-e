import InitECandidate.Runtime.AuthorizationsStepBound
namespace InitECandidate.Runtime

theorem authorizationStepCost_mono_left (left right inputLength : Nat) (bounded : left ≤ right) :
    authorizationStepCost left inputLength ≤ authorizationStepCost right inputLength := by
  have factor : (2 * left + 1) * 15 + 19 ≤ (2 * right + 1) * 15 + 19 := by omega
  have work := Nat.mul_le_mul bounded factor
  exact Nat.add_le_add_right (Nat.add_le_add_right work 92633) _

#print axioms authorizationStepCost_mono_left
end InitECandidate.Runtime
