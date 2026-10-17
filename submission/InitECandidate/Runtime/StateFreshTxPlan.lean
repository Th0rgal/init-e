import InitECandidate.Runtime.StateFreshTxSource
import InitECandidate.Runtime.HashNewFrontierFacts
namespace InitECandidate.Runtime
open Flapjack

def stateFreshTxNextTable (pointer : BitVec 64) (width capacity : Nat) : BitVec 64 :=
  allocationEnd (htabNewOrderPos pointer (BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity)) (BitVec.ofNat 64 capacity * 8)

def stateFreshTxAllocationBudget : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | (_,capacity,_) :: rest => 81 * capacity + 114 + stateFreshTxAllocationBudget rest

def stateFreshTxClockBudget : List (Nat × Nat × Nat) → Nat
  | [] => 0
  | (_,capacity,_) :: rest => capacity + 8 + stateFreshTxClockBudget rest

/-- The constructor frontier advances monotonically and obeys the same numeric
budget used to reserve space for all following transaction tables. -/
theorem stateFreshTx_next_table_bounds (pointer : BitVec 64) (width capacity : Nat)
    (widthBound : width ≤ 52) (capacityBound : capacity < 2 ^ 64)
    (budget : pointer.toNat + 81 * capacity + 114 ≤ 33806089496) :
    pointer.toNat + 72 ≤ (stateFreshTxNextTable pointer width capacity).toNat ∧
      (stateFreshTxNextTable pointer width capacity).toNat ≤ pointer.toNat + 81 * capacity + 114 ∧
      (stateFreshTxNextTable pointer width capacity).toNat % 8 = 0 := by
  have widthNat : (BitVec.ofNat 64 width).toNat = width := Nat.mod_eq_of_lt (by omega)
  have capacityNat : (BitVec.ofNat 64 capacity).toNat = capacity := Nat.mod_eq_of_lt capacityBound
  have keyBound : (BitVec.ofNat 64 width).toNat ≤ 52 := by omega
  have wordBudget : pointer.toNat + 81 * (BitVec.ofNat 64 capacity).toNat + 114 ≤ 33806089496 := by omega
  have plan := htabNew_allocation_plan_safe pointer (BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity) keyBound wordBudget
  have frontier := htabNew_frontier_facts pointer (BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity) keyBound wordBudget
  obtain ⟨_,_,_,_,beforeValues,valuesBefore,usedBefore,orderBefore,endBound⟩ :=
    htabNew_insertion_layout pointer (BitVec.ofNat 64 width) (BitVec.ofNat 64 capacity) keyBound wordBudget
  have upper : (stateFreshTxNextTable pointer width capacity).toNat ≤ pointer.toNat + 81 * capacity + 114 := by
    simpa only [stateFreshTxNextTable,htabNewOrderPos,htabNewOrder,htabNewUsed,htabNewValues,
      htabNewAllocationSizes,allocationPlanEnd,capacityNat] using plan.2
  exact ⟨by change pointer.toNat + 72 ≤ (allocationEnd _ _).toNat; omega,upper,frontier.2.2⟩

/-- Exact remaining constructor costs in the frozen fresh-transaction source. -/
theorem stateFreshTx_remaining_budgets :
    stateFreshTxAllocationBudget stateFreshTxRemainingTables = 17646 ∧
      stateFreshTxClockBudget stateFreshTxRemainingTables = 264 := by decide

#print axioms stateFreshTx_next_table_bounds
#print axioms stateFreshTx_remaining_budgets
end InitECandidate.Runtime
