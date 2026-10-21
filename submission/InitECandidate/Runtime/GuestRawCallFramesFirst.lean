import InitECandidate.Runtime.RawCallFrameEligibility
import InitECandidate.Proofs.BackendStages.Chunk64_79

namespace InitECandidate.Runtime.StackRawCall
open InitECandidate.Proofs.BackendStages
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

theorem rawFrames_Chunk64_79 : rawCallCodeFramesSupported Chunk64_79.bodies = true := by
  decide_cbv

#print axioms rawFrames_Chunk64_79
end InitECandidate.Runtime.StackRawCall
