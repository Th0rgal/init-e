import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass591_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass591_5 : WordLangProgHOL (BitVec 64) :=
word591_3_2925
theorem pass591_5_eq : WordCopy.copyProp (pass591_4) = pass591_5 := by
  kernel_rfl
#print axioms pass591_5_eq
end InitECandidate.Proofs.WordStages
