import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass798_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass798_4 : WordLangProgHOL (BitVec 64) :=
word798_3_1152
theorem pass798_4_eq : WordCse.wordCommonSubexpElim (pass798_3) = pass798_4 := by
  kernel_rfl
#print axioms pass798_4_eq
end InitECandidate.Proofs.WordStages
