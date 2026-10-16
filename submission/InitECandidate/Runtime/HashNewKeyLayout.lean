import InitECandidate.Runtime.HashNewLayout
namespace InitECandidate.Runtime
open Flapjack

/-- The constructor key allocation is aligned, follows its header, and ends
before the occupancy allocation with no overflow in the capacity product. -/
theorem htabNew_key_layout (table keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496) :
    let keys := allocationEnd table 72
    let stride := allocationEnd 0 keyLength
    keys.toNat % 8 = 0 ∧ stride.toNat % 8 = 0 ∧
      keyLength.toNat ≤ stride.toNat ∧ table.toNat + 72 ≤ keys.toNat ∧
      keys.toNat + capacity.toNat * stride.toNat ≤ (htabNewUsed table keyLength capacity).toNat := by
  have safe := (htabNew_allocation_plan_safe table keyLength capacity keyBound budget).1
  obtain ⟨g1,b1,g2,b2,g3,b3,rest⟩ := safe
  have header := allocationEnd_covers table 72
    (allocationGuard_sum_bound table 72 (by omega) g1)
  have keySum := allocationGuard_sum_bound (allocationEnd table 72) (capacity * allocationEnd 0 keyLength) b1 g2
  have keys := allocationEnd_covers (allocationEnd table 72) (capacity * allocationEnd 0 keyLength) keySum
  have values := allocationEnd_covers (htabNewValues table keyLength capacity) (capacity * 8)
    (allocationGuard_sum_bound _ _ b2 g3)
  have stride := htabNew_stride_bound keyLength keyBound
  have productBound := Nat.mul_le_mul_left capacity.toNat stride.2.1
  have product : (capacity * allocationEnd 0 keyLength).toNat =
      capacity.toNat * (allocationEnd 0 keyLength).toNat :=
    BitVec.toNat_mul_of_lt (by omega)
  dsimp only
  refine ⟨header.2.2,stride.2.2,stride.1,?_,?_⟩
  · simpa using header.1
  · rw [product] at keys
    have lowerKeys := keys.1
    have lowerValues := values.1
    change (allocationEnd table 72).toNat + capacity.toNat * (allocationEnd 0 keyLength).toNat ≤
      (htabNewValues table keyLength capacity).toNat at lowerKeys
    change (htabNewValues table keyLength capacity).toNat + (capacity * 8).toNat ≤
      (htabNewUsed table keyLength capacity).toNat at lowerValues
    omega

#print axioms htabNew_key_layout
end InitECandidate.Runtime
