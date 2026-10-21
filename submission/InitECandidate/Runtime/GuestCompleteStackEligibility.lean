import InitECandidate.Runtime.GuestStackCodeEligibility
namespace InitECandidate.Runtime.StackToLab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

/-- All emitted builtin stubs, including the unused constant-copy stub,
are in the native extraction grammar after stack removal. -/
theorem guest_removed_stubs_supported :
    InitECandidate.Proofs.BackendStages.RemovedStubs.all (fun entry => executionSupported entry.2) = true := by
  decide_cbv

theorem guest_complete_stack_supported :
    InitECandidate.Proofs.BackendStages.Removed.stack.all (fun entry => executionSupported entry.2) = true := by
  rw [InitECandidate.Proofs.BackendStages.Removed.stack, List.all_append]
  simp only [guest_removed_stubs_supported, guest_stack_supported, Bool.and_self]

theorem guest_complete_stack_code_supported : ExecutionCodeSupported
    (Flapjack.sptFromAList InitECandidate.Proofs.BackendStages.Removed.stack) :=
  executionCodeSupported_fromAList _ guest_complete_stack_supported

#print axioms guest_removed_stubs_supported
#print axioms guest_complete_stack_supported
#print axioms guest_complete_stack_code_supported
end InitECandidate.Runtime.StackToLab
