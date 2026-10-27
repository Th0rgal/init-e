import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass459_9
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass459_10 : WordLangProgHOL (BitVec 64) :=
word459_9_1200
theorem pass459_10_eq : WordRemove.removeMustTerminate (pass459_9) = pass459_10 := by
  kernel_rfl
#print axioms pass459_10_eq
end InitECandidate.Proofs.WordStages
