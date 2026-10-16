import InitECandidate.Runtime.HashNewAllocationPlan
namespace InitECandidate.Runtime
open Flapjack

/-- Original growth allocates five arrays at twice the old capacity. -/
def htabGrowAllocationSizes (capacity stride : BitVec 64) : List (BitVec 64) :=
  [(capacity * 2) * stride,(capacity * 2) * 8,capacity * 2,(capacity * 2) * 8,(capacity * 2) * 8]

/-- A growth byte budget covers all five actual requests and their rounding,
while ensuring that source capacity doubling and products cannot wrap. -/
theorem htabGrow_allocation_plan_safe (pointer capacity stride : BitVec 64)
    (strideBound : stride.toNat ≤ 56)
    (budget : pointer.toNat + 162 * capacity.toNat + 35 ≤ 33806089496) :
    (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat ∧
      AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride) ∧
      (allocationPlanEnd pointer (htabGrowAllocationSizes capacity stride)).toNat ≤
        pointer.toNat + 162 * capacity.toNat + 35 := by
  have doubled : (capacity * (2 : BitVec 64)).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)]
    change capacity.toNat * 2 = 2 * capacity.toNat
    omega
  have keyBound := Nat.mul_le_mul_left (2 * capacity.toNat) strideBound
  have keys : ((capacity * 2) * stride).toNat = 2 * capacity.toNat * stride.toNat := by
    rw [BitVec.toNat_mul_of_lt (by rw [doubled]; omega),doubled]
  have words : ((capacity * 2) * (8 : BitVec 64)).toNat = 2 * capacity.toNat * 8 := by
    rw [BitVec.toNat_mul_of_lt (by rw [doubled]; change 2 * capacity.toNat * 8 < 2 ^ 64; omega),doubled]
    rfl
  have sizes : (htabGrowAllocationSizes capacity stride |>.map BitVec.toNat).sum ≤ 162 * capacity.toNat := by
    simp only [htabGrowAllocationSizes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,keys,words,doubled]
    omega
  have length : (htabGrowAllocationSizes capacity stride).length = 5 := rfl
  have planBudget : pointer.toNat + (htabGrowAllocationSizes capacity stride |>.map BitVec.toNat).sum +
      7 * (htabGrowAllocationSizes capacity stride).length ≤ 33806089496 := by
    rw [length]
    omega
  have plan := allocationPlan_safe (htabGrowAllocationSizes capacity stride) pointer planBudget
  exact ⟨doubled,plan.1,by have upper := plan.2.2; rw [length] at upper; omega⟩

#print axioms htabGrow_allocation_plan_safe
end InitECandidate.Runtime
