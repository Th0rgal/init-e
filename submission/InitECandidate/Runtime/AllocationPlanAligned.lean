import InitECandidate.Runtime.AllocationPlanFacts
import InitECandidate.Runtime.HashNewAllocationPlan
namespace InitECandidate.Runtime
open Flapjack

/-- Aligned requests from an aligned frontier consume exactly their byte sum;
no per-allocation padding reserve is needed. -/
theorem allocationPlan_safe_aligned (sizes : List (BitVec 64)) (pointer : BitVec 64)
    (aligned : pointer.toNat % 8 = 0)
    (alignedSizes : ∀ size ∈ sizes, size.toNat % 8 = 0)
    (bounded : pointer.toNat + (sizes.map BitVec.toNat).sum ≤ 33806089496) :
    AllocationPlanSafe pointer sizes ∧
      (allocationPlanEnd pointer sizes).toNat = pointer.toNat + (sizes.map BitVec.toNat).sum := by
  induction sizes generalizing pointer with
  | nil => simpa [AllocationPlanSafe,allocationPlanEnd] using bounded
  | cons size rest ih =>
    have sum : pointer.toNat + size.toNat ≤ 33806089496 := by
      simp only [List.map_cons,List.sum_cons] at bounded
      omega
    have sizeAligned := alignedSizes size (by simp)
    have next := allocationEnd_aligned_toNat pointer size sum aligned sizeAligned
    have restAligned : ∀ item ∈ rest, item.toNat % 8 = 0 := by
      intro item member
      exact alignedSizes item (by simp [member])
    have restBound : (allocationEnd pointer size).toNat + (rest.map BitVec.toNat).sum ≤ 33806089496 := by
      rw [next]
      simp only [List.map_cons,List.sum_cons] at bounded
      omega
    obtain ⟨tail,finish⟩ := ih (allocationEnd pointer size) (allocationEnd_covers pointer size sum).2.2 restAligned restBound
    refine ⟨⟨allocationGuard_of_sum_bound pointer size sum,by rw [next]; omega,tail⟩,?_⟩
    simp only [allocationPlanEnd,List.map_cons,List.sum_cons]
    rw [finish,next]
    omega

/-- The literal storage constructor requests exactly 528 aligned bytes. -/
theorem storageTable_allocation_sizes : htabNewAllocationSizes (32 : BitVec 64) 8 =
    [72,256,64,8,64,64] := by decide

/-- A storage table fits exactly when 528 bytes remain at the aligned frontier. -/
theorem storageTable_safe_plan_iff (pointer : BitVec 64)
    (bounded : pointer.toNat ≤ 33806089496) (aligned : pointer.toNat % 8 = 0) :
    AllocationPlanSafe pointer (htabNewAllocationSizes 32 8) ↔ pointer.toNat + 528 ≤ 33806089496 := by
  have bytes : ((htabNewAllocationSizes (32 : BitVec 64) 8).map BitVec.toNat).sum = 528 := by decide
  constructor
  · intro safe
    have facts := allocationPlan_facts _ pointer safe bounded aligned
    rw [bytes] at facts
    omega
  · intro space
    apply (allocationPlan_safe_aligned _ pointer aligned ?_ ?_).1
    · rw [storageTable_allocation_sizes]
      intro size member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [bytes]; exact space

#print axioms allocationPlan_safe_aligned
#print axioms storageTable_allocation_sizes
#print axioms storageTable_safe_plan_iff
end InitECandidate.Runtime
