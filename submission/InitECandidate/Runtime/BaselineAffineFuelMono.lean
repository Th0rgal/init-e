import InitECandidate.Runtime.BaselineAffineNative
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime

theorem baselineNativeAffineFuel_mono (a b : Nat) (less : a ≤ b) :
    baselineNativeAffineFuel a ≤ baselineNativeAffineFuel b := by
  have word : baselineWordAffineFuel a ≤ baselineWordAffineFuel b := by
    unfold baselineWordAffineFuel
    have scaled := Nat.mul_le_mul_left (2 * baselineWordLimit + 2) less
    omega
  have raw : baselineRawAffineFuel a ≤ baselineRawAffineFuel b := Nat.mul_le_mul_left 2 word
  have removal := Nat.mul_le_mul_left baselineBitmapScale
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * baselineRemovalLimit + 2) raw) (2 * baselineRemovalLimit))
  have removed : baselineRemovedFullAffineFuel a ≤ baselineRemovedFullAffineFuel b :=
    Nat.add_le_add_right (Nat.add_le_add raw removal) 1
  exact Nat.mul_le_mul_left 14467153
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * baselineNamedLimit + 3) removed) _)

#print axioms baselineNativeAffineFuel_mono
end InitECandidate.Runtime
