import InitECandidate.Runtime.HashNewLayout
import InitECandidate.Runtime.HashGrowSafePlanLayout
namespace InitECandidate.Runtime
open Flapjack

/-- The constructor allocates the entire key array before the value array. -/
theorem htabNew_keys_before_values (table keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496) :
    (allocationEnd table 72).toNat + capacity.toNat * (allocationEnd 0 keyLength).toNat ≤
      (htabNewValues table keyLength capacity).toNat := by
  have safe := (htabNew_allocation_plan_safe table keyLength capacity keyBound budget).1
  obtain ⟨_,before,guard,_,_⟩ := safe
  have stride := htabNew_stride_bound keyLength keyBound
  have productBound := Nat.mul_le_mul_left capacity.toNat stride.2.1
  have product : (capacity * allocationEnd 0 keyLength).toNat =
      capacity.toNat * (allocationEnd 0 keyLength).toNat :=
    BitVec.toNat_mul_of_lt (by omega)
  have covers := allocationEnd_covers (allocationEnd table 72) (capacity * allocationEnd 0 keyLength)
    (allocationGuard_sum_bound _ _ before guard)
  simpa only [htabNewValues,allocationPlanEnd,product] using covers.1

/-- A safe growth plan retains key/value separation without a conservative
allocation budget, including all rounding performed by the original allocator. -/
theorem htabGrow_keys_before_values (pointer capacity stride : BitVec 64)
    (pointerBound : pointer.toNat ≤ 33806089496)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (strideBound : stride.toNat ≤ 56)
    (safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)) :
    pointer.toNat + (capacity * 2).toNat * stride.toNat ≤
      (htabGrowValues pointer capacity stride).toNat := by
  obtain ⟨guard,_,_⟩ := safe
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 :=
    BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have productBound := Nat.mul_le_mul_left (capacity.toNat * 2) strideBound
  have product : ((capacity * 2) * stride).toNat = (capacity * 2).toNat * stride.toNat :=
    BitVec.toNat_mul_of_lt (by rw [doubled]; omega)
  have covers := allocationEnd_covers pointer ((capacity * 2) * stride)
    (allocationGuard_sum_bound _ _ pointerBound guard)
  simpa only [htabGrowValues,product] using covers.1

#print axioms htabNew_keys_before_values
#print axioms htabGrow_keys_before_values
end InitECandidate.Runtime
