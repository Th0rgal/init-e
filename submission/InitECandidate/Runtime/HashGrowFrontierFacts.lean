import InitECandidate.Runtime.HashGrowSafePlanLayout
import InitECandidate.Runtime.HashTableHeapFrontier32
import InitECandidate.Runtime.AllocationPlanFacts
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The exact final allocation of a safe growth plan covers the reverse-order
array and provides the next aligned, bounded heap frontier. -/
theorem htabGrow_frontier_facts (pointer capacity stride : BitVec 64)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride)) :
    let last := htabGrowOrderPos pointer capacity stride
    let next := allocationEnd last ((capacity * 2) * 8)
    last.toNat + (capacity * 2).toNat * 8 ≤ next.toNat ∧
      next.toNat ≤ 33806089496 ∧ next.toNat % 8 = 0 := by
  obtain ⟨_,_,_,_,_,_,_,before,guard,bounded,_⟩ := safe
  have doubled : (capacity * (2 : BitVec 64)).toNat = capacity.toNat * 2 :=
    BitVec.toNat_mul_of_lt (by change capacity.toNat * 2 < 2 ^ 64; omega)
  have words : ((capacity * 2) * (8 : BitVec 64)).toNat = (capacity * 2).toNat * 8 := by
    apply BitVec.toNat_mul_of_lt
    rw [doubled]
    change capacity.toNat * 2 * 8 < 2 ^ 64
    omega
  have covers := allocationEnd_covers (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)
    (allocationGuard_sum_bound _ _ before guard)
  rw [words] at covers
  exact ⟨covers.1,bounded,covers.2.2⟩

theorem htabGrow_heap_frontier32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer capacity stride : BitVec 64)
    (capacityBound : capacity.toNat ≤ 33806089496)
    (safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8))))) :
    HashTableHeapFrontier32 (htabGrowOrderPos pointer capacity stride) (capacity * 2)
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) state := by
  have facts := htabGrow_frontier_facts pointer capacity stride capacityBound safe
  exact ⟨heap,facts.1,facts.2.1,facts.2.2⟩

#print axioms htabGrow_frontier_facts
#print axioms htabGrow_heap_frontier32

/-- Existing tables remain below the new heap frontier after another table's
safe growth allocations. The supplied post-state must have the actual endpoint. -/
theorem HashTableHeapFrontier32.after_growth_plan {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (oldOrderPos oldCapacity pointer capacity stride : BitVec 64)
    (frontier : HashTableHeapFrontier32 oldOrderPos oldCapacity pointer state)
    (safe : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (heap : post.globals.lookup (ofString "heap_ptr") = some (.val (.word
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8))))) :
    HashTableHeapFrontier32 oldOrderPos oldCapacity
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post := by
  have facts := allocationPlan_facts (htabGrowAllocationSizes capacity stride) pointer
    safe frontier.bounded frontier.aligned
  have monotone : pointer.toNat ≤
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)).toNat := by
    have lower := facts.1
    change pointer.toNat + _ ≤
      (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)).toNat at lower
    omega
  exact frontier.advance state post oldOrderPos oldCapacity pointer _ heap monotone facts.2.1 facts.2.2

#print axioms HashTableHeapFrontier32.after_growth_plan
end InitECandidate.Runtime
