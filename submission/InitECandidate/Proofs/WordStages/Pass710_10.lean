import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass710_9
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass710_10 : WordLangProgHOL (BitVec 64) :=
word710_9_1610
theorem pass710_10_eq : WordRemove.removeMustTerminate (pass710_9) = pass710_10 := by
  kernel_rfl
#print axioms pass710_10_eq
end InitECandidate.Proofs.WordStages
