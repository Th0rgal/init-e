import InitECandidate.Runtime.StackDirectCallClosure
import InitECandidate.Proofs.BackendStages.Alloc
namespace InitECandidate.Runtime.StackToLab
open Flapjack
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000

/-- The installed guest, including its builtin stubs, never calls the
constant-copy stub and uses no indirect call destinations. -/
theorem guest_direct_calls_avoid_constants :
    InitECandidate.Proofs.BackendStages.Alloc.stack.all
      (fun entry => directCallsAvoid storeConstsStubLocation entry.2) = true := by
  decide_cbv

#print axioms guest_direct_calls_avoid_constants
end InitECandidate.Runtime.StackToLab
