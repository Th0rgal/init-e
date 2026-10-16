import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack

/-- The heap pointer after a sequence of original rounded allocations. -/
def allocationPlanEnd (pointer : BitVec 64) : List (BitVec 64) → BitVec 64
  | [] => pointer
  | size :: rest => allocationPlanEnd (allocationEnd pointer size) rest

/-- Both original allocator guards hold at every point in a plan. -/
def AllocationPlanSafe (pointer : BitVec 64) : List (BitVec 64) → Prop
  | [] => pointer.toNat ≤ 33806089496
  | size :: rest => size ≤ (33806089496 : BitVec 64) - pointer ∧
      (allocationEnd pointer size).toNat ≤ 33806089496 ∧
      AllocationPlanSafe (allocationEnd pointer size) rest

/-- A natural byte budget plus seven bytes per allocation proves that the
whole allocation plan succeeds, not just its first request. -/
theorem allocationPlan_safe (sizes : List (BitVec 64)) (pointer : BitVec 64)
    (budget : pointer.toNat + (sizes.map BitVec.toNat).sum + 7 * sizes.length ≤ 33806089496) :
    AllocationPlanSafe pointer sizes ∧
      pointer.toNat + (sizes.map BitVec.toNat).sum ≤ (allocationPlanEnd pointer sizes).toNat ∧
      (allocationPlanEnd pointer sizes).toNat ≤
        pointer.toNat + (sizes.map BitVec.toNat).sum + 7 * sizes.length := by
  induction sizes generalizing pointer with
  | nil => simpa [AllocationPlanSafe,allocationPlanEnd] using budget
  | cons size rest ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons] at budget ⊢
    have padded : pointer.toNat + size.toNat + 7 ≤ 33806089496 := by omega
    obtain ⟨guard,finish,covered,aligned⟩ := allocation_success_bounds pointer size padded
    have upper : (allocationEnd pointer size).toNat ≤ pointer.toNat + size.toNat + 7 := by
      have rounded := allocationEnd_covers pointer size (by omega)
      omega
    have restBudget : (allocationEnd pointer size).toNat + (rest.map BitVec.toNat).sum +
        7 * rest.length ≤ 33806089496 := by omega
    obtain ⟨safe,lower,last⟩ := ih (allocationEnd pointer size) restBudget
    exact ⟨⟨guard,finish,safe⟩,by simpa [allocationPlanEnd] using (show
      pointer.toNat + (size.toNat + (rest.map BitVec.toNat).sum) ≤
        (allocationPlanEnd (allocationEnd pointer size) rest).toNat from by omega),
      by simpa [allocationPlanEnd] using (show
        (allocationPlanEnd (allocationEnd pointer size) rest).toNat ≤
          pointer.toNat + (size.toNat + (rest.map BitVec.toNat).sum) + 7 * (rest.length + 1) from by omega)⟩

#print axioms allocationPlan_safe
end InitECandidate.Runtime
