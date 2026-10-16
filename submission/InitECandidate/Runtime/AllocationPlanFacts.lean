import InitECandidate.Runtime.AllocationPlan
namespace InitECandidate.Runtime
open Flapjack

/-- Successful allocation plans advance past all requested bytes and retain
heap bounds and alignment. -/
theorem allocationPlan_facts (sizes : List (BitVec 64)) (pointer : BitVec 64)
    (safe : AllocationPlanSafe pointer sizes) (bounded : pointer.toNat ≤ 33806089496)
    (aligned : pointer.toNat % 8 = 0) :
    pointer.toNat + (sizes.map BitVec.toNat).sum ≤ (allocationPlanEnd pointer sizes).toNat ∧
      (allocationPlanEnd pointer sizes).toNat ≤ 33806089496 ∧
      (allocationPlanEnd pointer sizes).toNat % 8 = 0 := by
  induction sizes generalizing pointer with
  | nil => simpa [allocationPlanEnd] using (show pointer.toNat ≤ pointer.toNat ∧
      pointer.toNat ≤ 33806089496 ∧ pointer.toNat % 8 = 0 from ⟨Nat.le_refl _,bounded,aligned⟩)
  | cons size rest ih =>
    obtain ⟨guard,finish,tail⟩ := safe
    have cover := allocationEnd_covers pointer size (allocationGuard_sum_bound pointer size bounded guard)
    obtain ⟨lower,last,lastAligned⟩ := ih (allocationEnd pointer size) tail finish cover.2.2
    refine ⟨?_,last,lastAligned⟩
    simp only [allocationPlanEnd,List.map_cons,List.sum_cons]
    omega

#print axioms allocationPlan_facts
end InitECandidate.Runtime
