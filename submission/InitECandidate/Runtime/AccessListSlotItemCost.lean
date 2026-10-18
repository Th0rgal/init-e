import InitECandidate.Runtime.AccessListSlotItemBound
namespace InitECandidate.Runtime

theorem accessSlotItemCost_mono {first second : Nat} (bounded : first ≤ second) :
    accessSlotItemCost first ≤ accessSlotItemCost second := by
  have factor : (2 * first + 1) * 15 + 19 ≤ (2 * second + 1) * 15 + 19 := by omega
  have quadratic := Nat.mul_le_mul bounded factor
  exact Nat.add_le_add (Nat.add_le_add_right quadratic 92634) (accessSlotSlicesCost_mono bounded)

#print axioms accessSlotItemCost_mono
end InitECandidate.Runtime
