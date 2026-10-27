import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass655_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass655_5 : WordLangProgHOL (BitVec 64) :=
word655_3_1227
theorem pass655_5_eq : WordCopy.copyProp (pass655_4) = pass655_5 := by
  kernel_rfl
#print axioms pass655_5_eq
end InitECandidate.Proofs.WordStages
