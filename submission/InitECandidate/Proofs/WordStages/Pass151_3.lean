import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass151_2
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass151_3 : WordLangProgHOL (BitVec 64) :=
word151_2_13074
theorem pass151_3_eq : WordAlloc.removeDeadProg (pass151_2) = pass151_3 := by
  kernel_rfl
#print axioms pass151_3_eq
end InitECandidate.Proofs.WordStages
