import InitECandidate.Runtime.GuestRemovalEligibility
namespace InitECandidate.Runtime.StackToLab
open Flapjack
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 10000000

/-- Allocation and exception stubs have supported lowering. The installed
constant-copy stub is excluded here and ruled unreachable separately. -/
theorem guest_nonconstant_stubs_supported :
    InitECandidate.Proofs.BackendStages.AllocStubs.all
      (fun entry => decide (entry.1 = storeConstsStubLocation) || removalSupported entry.2) = true := by
  decide_cbv

theorem guest_nonconstant_code_supported :
    InitECandidate.Proofs.BackendStages.Alloc.stack.all
      (fun entry => decide (entry.1 = storeConstsStubLocation) || removalSupported entry.2) = true := by
  rw [InitECandidate.Proofs.BackendStages.Alloc.stack, List.all_append]
  simp only [Bool.and_eq_true]
  refine ⟨guest_nonconstant_stubs_supported, ?_⟩
  apply List.all_eq_true.mpr
  intro entry member
  have supported := List.all_eq_true.mp guest_removal_supported entry member
  simp only [supported, Bool.or_true]

#print axioms guest_nonconstant_stubs_supported
#print axioms guest_nonconstant_code_supported
end InitECandidate.Runtime.StackToLab
