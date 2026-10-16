import InitECandidate.Runtime.HashNewSeparation
import InitECandidate.Runtime.HashNewValuesAllocation
namespace InitECandidate.Runtime
open Flapjack

def htabNewOrder (table keyLength capacity : BitVec 64) : BitVec 64 :=
  allocationEnd (htabNewUsed table keyLength capacity) capacity

def htabNewOrderPos (table keyLength capacity : BitVec 64) : BitVec 64 :=
  allocationEnd (htabNewOrder table keyLength capacity) (capacity * 8)

/-- The original six-allocation constructor plan establishes the aligned,
ordered regions required by insertion, including the reverse-order array. -/
theorem htabNew_insertion_layout (table keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496) :
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
  have safe := (htabNew_allocation_plan_safe table keyLength capacity keyBound budget).1
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

#print axioms htabNew_insertion_layout
end InitECandidate.Runtime
