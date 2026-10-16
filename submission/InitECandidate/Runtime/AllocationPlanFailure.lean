import InitECandidate.Runtime.AllocationPlan
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack

/-- Every finite allocation plan either succeeds or has a first excessive
request after a safe prior. Rounding cannot create another failure kind. -/
theorem allocationPlan_safe_or_first_failure (sizes : List (BitVec 64)) (pointer : BitVec 64)
    (bounded : pointer.toNat ≤ 33806089496) :
    AllocationPlanSafe pointer sizes ∨
      ∃ prior : List (BitVec 64), ∃ size suffix,
        sizes = prior ++ size :: suffix ∧ AllocationPlanSafe pointer prior ∧
        (allocationPlanEnd pointer prior).toNat ≤ 33806089496 ∧
        ((33806089496 : BitVec 64) - allocationPlanEnd pointer prior).toNat < size.toNat := by
  induction sizes generalizing pointer with
  | nil => exact Or.inl bounded
  | cons size rest ih =>
    by_cases request : size ≤ (33806089496 : BitVec 64) - pointer
    · have within := allocationEnd_within_heap pointer size bounded request
      rcases ih (allocationEnd pointer size) within with safe | failed
      · exact Or.inl ⟨request,within,safe⟩
      · obtain ⟨prior,failedSize,suffix,split,safe,endBound,rejected⟩ := failed
        refine Or.inr ⟨size :: prior,failedSize,suffix,?_,?_,endBound,rejected⟩
        · simp only [List.cons_append,split]
        · exact ⟨request,within,safe⟩
    · have rejected : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat := by
        have notLe : ¬size.toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat := fun le => request (BitVec.le_def.mpr le)
        omega
      exact Or.inr ⟨[],size,rest,rfl,bounded,bounded,rejected⟩

/-- The first failing allocation is preceded by fewer allocations than the
length of the complete plan. -/
theorem allocationPlan_failure_prefix_length (sizes prior : List (BitVec 64))
    (size : BitVec 64) (suffix : List (BitVec 64))
    (split : sizes = prior ++ size :: suffix) : prior.length < sizes.length := by
  rw [split,List.length_append,List.length_cons]
  omega

#print axioms allocationPlan_safe_or_first_failure
#print axioms allocationPlan_failure_prefix_length
end InitECandidate.Runtime
