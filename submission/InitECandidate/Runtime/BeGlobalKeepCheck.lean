import InitECandidate.Runtime.PtBeKeepGD
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
/-- Kernel-computed check over the actual original source bodies. Functions
outside the explicit transitive assignment callers preserve the be global. -/
theorem be_global_keep_checked : BeKeep := by
 unfold BeKeep
 decide_cbv

#print axioms be_global_keep_checked
end InitECandidate.Runtime
