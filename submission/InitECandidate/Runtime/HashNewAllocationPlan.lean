import InitECandidate.Runtime.AllocationPlan
import InitECandidate.Runtime.HashNewHeader
namespace InitECandidate.Runtime
open Flapjack

/-- Sizes of the header, keys, values, occupancy, order and reverse-order
allocations in the original hash-table constructor, in execution order. -/
def htabNewAllocationSizes (keyLength capacity : BitVec 64) : List (BitVec 64) :=
  [72,capacity * allocationEnd 0 keyLength,capacity * 8,capacity,capacity * 8,capacity * 8]

/-- With challenge key widths, 81 bytes per slot plus 114 fixed bytes
cover every original constructor allocation and its rounding padding. -/
theorem htabNew_allocation_plan_safe (pointer keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52)
    (budget : pointer.toNat + 81 * capacity.toNat + 114 ≤ 33806089496) :
    AllocationPlanSafe pointer (htabNewAllocationSizes keyLength capacity) ∧
      (allocationPlanEnd pointer (htabNewAllocationSizes keyLength capacity)).toNat ≤
        pointer.toNat + 81 * capacity.toNat + 114 := by
  have stride := htabNew_stride_bound keyLength keyBound
  have keyBytes : capacity.toNat * (allocationEnd 0 keyLength).toNat ≤ capacity.toNat * 56 :=
    Nat.mul_le_mul_left capacity.toNat stride.2.1
  have keySmall : capacity.toNat * (allocationEnd 0 keyLength).toNat < 2 ^ 64 := by omega
  have eightSmall : capacity.toNat * (8 : BitVec 64).toNat < 2 ^ 64 := by
    change capacity.toNat * 8 < 2 ^ 64
    omega
  have keys := BitVec.toNat_mul_of_lt keySmall
  have words := BitVec.toNat_mul_of_lt eightSmall
  have sizes : (htabNewAllocationSizes keyLength capacity |>.map BitVec.toNat).sum ≤
      72 + 81 * capacity.toNat := by
    simp only [htabNewAllocationSizes,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,keys,words]
    change 72 + (capacity.toNat * (allocationEnd 0 keyLength).toNat +
      (capacity.toNat * 8 + (capacity.toNat + (capacity.toNat * 8 + (capacity.toNat * 8 + 0))))) ≤ _
    omega
  have length : (htabNewAllocationSizes keyLength capacity).length = 6 := rfl
  have allBudget : pointer.toNat + (htabNewAllocationSizes keyLength capacity |>.map BitVec.toNat).sum +
      7 * (htabNewAllocationSizes keyLength capacity).length ≤ 33806089496 := by
    rw [length]; omega
  have plan := allocationPlan_safe (htabNewAllocationSizes keyLength capacity) pointer allBudget
  exact ⟨plan.1,by have upper := plan.2.2; rw [length] at upper; omega⟩

#print axioms htabNew_allocation_plan_safe
end InitECandidate.Runtime
