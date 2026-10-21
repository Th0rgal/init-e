import InitECandidate.Runtime.GuestStackEligibility
import InitECandidate.Runtime.StackExecutionCodeEligibility
namespace InitECandidate.Runtime.StackToLab

theorem guest_stack_code_supported : ExecutionCodeSupported
    (Flapjack.sptFromAList InitECandidate.Proofs.BackendStages.Removed.bodies0) :=
  executionCodeSupported_fromAList _ guest_stack_supported

#print axioms guest_stack_code_supported
end InitECandidate.Runtime.StackToLab
