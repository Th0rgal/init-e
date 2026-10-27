import InitECandidate.Proofs.CseCheckpoints64.Proof5
import InitECandidate.Proofs.WordStages.Pass64_3
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints64
theorem checked : WordCse.wordCommonSubexpElim InitECandidate.Proofs.WordStages.pass64_3 = InitECandidate.Proofs.WordStages.word64_4_942 := by
  have h := congrArg Prod.snd node380_eq
  rw [knowledge0_def] at h
  exact h
#print axioms checked
end InitECandidate.Proofs.CseCheckpoints64
