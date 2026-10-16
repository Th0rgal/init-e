import InitECandidate.Runtime.WordCodeSize
import InitECandidate.Proofs.BackendStages.Chunk64_79
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime.WordToStack
open InitECandidate.Proofs.BackendStages
 theorem safe_Chunk64_79 : wordCodeNoInstall Chunk64_79.programs = true := by
  decide_cbv
#print axioms safe_Chunk64_79
end InitECandidate.Runtime.WordToStack
