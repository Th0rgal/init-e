import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass224_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass224_4 : WordLangProgHOL (BitVec 64) :=
word224_3_1372
theorem pass224_4_eq : WordCse.wordCommonSubexpElim (pass224_3) = pass224_4 := by
  kernel_rfl
#print axioms pass224_4_eq
end InitECandidate.Proofs.WordStages
