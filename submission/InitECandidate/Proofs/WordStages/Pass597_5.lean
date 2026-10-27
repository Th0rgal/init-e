import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass597_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def pass597_5 : WordLangProgHOL (BitVec 64) :=
word597_4_2925
theorem pass597_5_eq : WordCopy.copyProp (pass597_4) = pass597_5 := by
  kernel_rfl
#print axioms pass597_5_eq
end InitECandidate.Proofs.WordStages
