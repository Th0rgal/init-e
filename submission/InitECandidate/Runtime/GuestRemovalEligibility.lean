import InitECandidate.Runtime.StackRemovalEligibility
import InitECandidate.Proofs.BackendStages.Alloc
namespace InitECandidate.Runtime.StackToLab
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

/-- Concrete pre-removal guest artifact belongs to the quantitative grammar. -/
theorem guest_removal_supported :
    InitECandidate.Proofs.BackendStages.Alloc.bodies0.all (fun entry => removalSupported entry.2) = true := by
  decide_cbv

#print axioms guest_removal_supported
end InitECandidate.Runtime.StackToLab
