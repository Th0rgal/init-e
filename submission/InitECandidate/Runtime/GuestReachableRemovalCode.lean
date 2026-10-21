import InitECandidate.Runtime.GuestReachableRemovalSupport
import InitECandidate.Runtime.GuestDirectCallClosure
import InitECandidate.Runtime.StackRemovalReachableCode
namespace InitECandidate.Runtime.StackToLab
open Flapjack

/-- The complete installed guest code meets the reachability-aware
stack-removal premise, including allocation and exception builtin stubs. -/
theorem guest_reachable_removal_code : AvoidingRemovalCode storeConstsStubLocation
    (sptFromAList InitECandidate.Proofs.BackendStages.Alloc.stack) :=
  avoidingRemovalCode_fromAList _ _ guest_nonconstant_code_supported guest_direct_calls_avoid_constants

#print axioms guest_reachable_removal_code
end InitECandidate.Runtime.StackToLab
