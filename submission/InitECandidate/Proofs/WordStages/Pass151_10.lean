import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass151_9
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass151_10 : WordLangProgHOL (BitVec 64) :=
word151_9_7076
theorem pass151_10_eq : WordRemove.removeMustTerminate (pass151_9) = pass151_10 := by
  kernel_rfl
#print axioms pass151_10_eq
end InitECandidate.Proofs.WordStages
