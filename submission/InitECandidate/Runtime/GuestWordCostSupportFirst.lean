import InitECandidate.Runtime.WordCostSupported
import InitECandidate.Proofs.BackendStages.Chunk64_79
namespace InitECandidate.Runtime.WordToStack
open InitECandidate.Proofs.BackendStages
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000

theorem costSupported_Chunk64_79 : Chunk64_79.programs.all (fun entry => wordCostSupported entry.2.2) = true := by
  decide_cbv
#print axioms costSupported_Chunk64_79
end InitECandidate.Runtime.WordToStack
