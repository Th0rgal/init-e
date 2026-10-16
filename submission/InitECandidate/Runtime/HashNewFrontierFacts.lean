import InitECandidate.Runtime.HashNewLayout
import InitECandidate.Runtime.HashNewAllocationPlan
namespace InitECandidate.Runtime
open Flapjack

/-- The actual constructor endpoint covers the last array and is a bounded,
eight-byte-aligned frontier suitable for subsequent table growth. -/
theorem htabNew_frontier_facts (table keyLength capacity : BitVec 64)
    (keyBound : keyLength.toNat ≤ 52)
    (budget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496) :
    let frontier := allocationEnd (htabNewOrderPos table keyLength capacity) (capacity * 8)
    (htabNewOrderPos table keyLength capacity).toNat + capacity.toNat * 8 ≤ frontier.toNat ∧
      frontier.toNat ≤ 33806089496 ∧ frontier.toNat % 8 = 0 := by
  have safe := (htabNew_allocation_plan_safe table keyLength capacity keyBound budget).1
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

#print axioms htabNew_frontier_facts
end InitECandidate.Runtime
