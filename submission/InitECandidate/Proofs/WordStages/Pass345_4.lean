import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass345_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass345_4 : WordLangProgHOL (BitVec 64) :=
word345_3_1651
theorem pass345_4_eq : WordCse.wordCommonSubexpElim (pass345_3) = pass345_4 := by
  kernel_rfl
#print axioms pass345_4_eq
end InitECandidate.Proofs.WordStages
