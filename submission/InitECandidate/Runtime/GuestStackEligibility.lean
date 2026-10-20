import InitECandidate.Runtime.StackExecutionEligibility
import InitECandidate.Proofs.BackendStages.Removed
namespace InitECandidate.Runtime.StackToLab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

theorem guest_stack_supported :
    InitECandidate.Proofs.BackendStages.Removed.bodies0.all (fun entry => executionSupported entry.2) = true := by
  decide_cbv

#print axioms guest_stack_supported
end InitECandidate.Runtime.StackToLab
