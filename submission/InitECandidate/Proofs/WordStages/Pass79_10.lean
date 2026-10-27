import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass79_9
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass79_10 : WordLangProgHOL (BitVec 64) :=
word79_9_496
theorem pass79_10_eq : WordRemove.removeMustTerminate (pass79_9) = pass79_10 := by
  kernel_rfl
#print axioms pass79_10_eq
end InitECandidate.Proofs.WordStages
