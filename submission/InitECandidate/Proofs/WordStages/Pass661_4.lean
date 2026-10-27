import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass661_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass661_4 : WordLangProgHOL (BitVec 64) :=
word661_3_4713
theorem pass661_4_eq : WordCse.wordCommonSubexpElim (pass661_3) = pass661_4 := by
  kernel_rfl
#print axioms pass661_4_eq
end InitECandidate.Proofs.WordStages
