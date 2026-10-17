import InitECandidate.Runtime.HashNewKeyLayout
import InitECandidate.Runtime.HashNewFrontierFacts
namespace InitECandidate.Runtime
open Flapjack

/-- A successful occupancy request bounds the actual capacity independently
of multiplication wraparound or a conservative constructor reserve. -/
theorem htabNew_capacity_bound_of_safe_plan (table keyLength capacity : BitVec 64)
    (safe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity)) :
    capacity.toNat ≤ 33806089496 := by
  obtain ⟨_,_,_,_,_,usedBound,usedRequest,_⟩ := safe
  have sum := allocationGuard_sum_bound (htabNewUsed table keyLength capacity) capacity usedBound usedRequest
  omega

theorem htabNew_insertion_layout_of_safe_plan (table keyLength capacity : BitVec 64)
    (pointerBound : table.toNat ≤ 33806089496)
    (safe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity)) :
    let values := htabNewValues table keyLength capacity
    let used := htabNewUsed table keyLength capacity
    let order := htabNewOrder table keyLength capacity
    let orderPos := htabNewOrderPos table keyLength capacity
    values.toNat % 8 = 0 ∧ used.toNat % 8 = 0 ∧ order.toNat % 8 = 0 ∧ orderPos.toNat % 8 = 0 ∧
      table.toNat + 72 ≤ values.toNat ∧
      values.toNat + capacity.toNat * 8 ≤ used.toNat ∧
      used.toNat + capacity.toNat ≤ order.toNat ∧
      order.toNat + capacity.toNat * 8 ≤ orderPos.toNat ∧
      orderPos.toNat + capacity.toNat * 8 ≤ 33806089496 := by
  have capacityBound := htabNew_capacity_bound_of_safe_plan table keyLength capacity safe
  obtain ⟨g1,b1,g2,b2,g3,b3,g4,b4,g5,b5,g6,b6,last⟩ := safe
  have c1 := allocationEnd_covers table 72
    (allocationGuard_sum_bound table 72 (by omega) g1)
  have c2 := allocationEnd_covers (allocationEnd table 72) (capacity * allocationEnd 0 keyLength)
    (allocationGuard_sum_bound _ _ b1 g2)
  have c3 := allocationEnd_covers (htabNewValues table keyLength capacity) (capacity * 8)
    (allocationGuard_sum_bound _ _ b2 g3)
  have c4 := allocationEnd_covers (htabNewUsed table keyLength capacity) capacity
    (allocationGuard_sum_bound _ _ b3 g4)
  have c5 := allocationEnd_covers (htabNewOrder table keyLength capacity) (capacity * 8)
    (allocationGuard_sum_bound _ _ b4 g5)
  have c6 := allocationEnd_covers (htabNewOrderPos table keyLength capacity) (capacity * 8)
    (allocationGuard_sum_bound _ _ b5 g6)
  have words : (capacity * (8 : BitVec 64)).toNat = capacity.toNat * 8 := by
    have small : capacity.toNat * (8 : BitVec 64).toNat < 2 ^ 64 := by
      change capacity.toNat * 8 < 2 ^ 64
      omega
    exact BitVec.toNat_mul_of_lt small
  change (htabNewValues table keyLength capacity).toNat % 8 = 0 ∧ _
  have first : table.toNat + 72 ≤ (htabNewValues table keyLength capacity).toNat := by
    change table.toNat + 72 ≤ (allocationEnd (allocationEnd table 72) (capacity * allocationEnd 0 keyLength)).toNat
    have lower := c1.1
    change table.toNat + 72 ≤ (allocationEnd table 72).toNat at lower
    omega
  refine ⟨c2.2.2,c3.2.2,c4.2.2,c5.2.2,first,?_,c4.1,?_,?_⟩
  · simpa only [words,htabNewUsed,htabNewValues,allocationPlanEnd] using c3.1
  · simpa only [words,htabNewOrderPos] using c5.1
  · have lower := c6.1
    rw [words] at lower
    change (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)).toNat ≤ 33806089496 at b6
    omega


theorem htabNew_key_layout_of_safe_plan (table keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52)
    (pointerBound : table.toNat ≤ 33806089496)
    (safe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity)) :
    let keys := allocationEnd table 72
    let stride := allocationEnd 0 keyLength
    keys.toNat % 8 = 0 ∧ stride.toNat % 8 = 0 ∧
      keyLength.toNat ≤ stride.toNat ∧ table.toNat + 72 ≤ keys.toNat ∧
      keys.toNat + capacity.toNat * stride.toNat ≤ (htabNewUsed table keyLength capacity).toNat := by
  have capacityBound := htabNew_capacity_bound_of_safe_plan table keyLength capacity safe
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


theorem htabNew_frontier_facts_of_safe_plan (table keyLength capacity : BitVec 64)
    (_pointerBound : table.toNat ≤ 33806089496)
    (safe : AllocationPlanSafe table (htabNewAllocationSizes keyLength capacity)) :
    let frontier := allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)
    (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 ≤ frontier.toNat ∧
      frontier.toNat ≤ 33806089496 ∧ frontier.toNat % 8 = 0 := by
  have capacityBound := htabNew_capacity_bound_of_safe_plan table keyLength capacity safe
  obtain ⟨_,_,_,_,_,_,_,_,_,before,lastGuard,lastBound,_⟩ := safe
  have pointerBound : (htabNewOrderPos table keyLength capacity).toNat ≤ 33806089496 := before
  have guard : capacity * 8 ≤ (33806089496 : BitVec 64) - htabNewOrderPos table keyLength capacity := lastGuard
  have finish : (allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)).toNat ≤ 33806089496 := lastBound
  have product : (capacity * (8 : BitVec 64)).toNat = capacity.toNat * 8 := by
    exact BitVec.toNat_mul_of_lt (by change capacity.toNat * 8 < 2 ^ 64; omega)
  have covers := allocationEnd_covers (htabNewOrderPos table keyLength capacity) (capacity * 8)
    (allocationGuard_sum_bound _ _ pointerBound guard)
  rw [product] at covers
  exact ⟨covers.1,finish,covers.2.2⟩


#print axioms htabNew_capacity_bound_of_safe_plan
#print axioms htabNew_insertion_layout_of_safe_plan
#print axioms htabNew_key_layout_of_safe_plan
#print axioms htabNew_frontier_facts_of_safe_plan
end InitECandidate.Runtime
