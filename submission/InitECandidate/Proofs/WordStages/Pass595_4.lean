import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass595_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass595_4 : WordLangProgHOL (BitVec 64) :=
word595_3_2925
theorem pass595_4_eq : WordCse.wordCommonSubexpElim (pass595_3) = pass595_4 := by
  kernel_rfl
#print axioms pass595_4_eq
end InitECandidate.Proofs.WordStages
