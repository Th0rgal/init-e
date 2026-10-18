import InitECandidate.Runtime.AuthorizationsBodyBound
namespace InitECandidate.Runtime

/-- Widening the input ceiling also widens the complete decoder clock budget. -/
theorem authorizationBodyCost_mono {first second : Nat} (bounded : first ≤ second) :
    authorizationBodyCost first ≤ authorizationBodyCost second := by
  have factor : (2 * first + 1) * 15 + 19 ≤ (2 * second + 1) * 15 + 19 := by omega
  have quadratic := Nat.mul_le_mul bounded factor
  have bytes := Nat.mul_le_mul_right 12 bounded
  have fields := Nat.mul_le_mul_left 6 (Nat.add_le_add_right quadratic 92668)
  have inner : authorizationInnerSlicesCost first first ≤ authorizationInnerSlicesCost second second := by
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add quadratic bytes) 4) fields
  have step : authorizationStepCost first first ≤ authorizationStepCost second second := by
    exact Nat.add_le_add (Nat.add_le_add_right quadratic 92633) inner
  have iterations := Nat.mul_le_mul bounded (Nat.add_le_add_right step 1)
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add quadratic bytes) 4)
    (Nat.add_le_add_right iterations 2)

#print axioms authorizationBodyCost_mono
end InitECandidate.Runtime
