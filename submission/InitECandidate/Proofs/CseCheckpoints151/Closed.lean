import InitECandidate.Proofs.CseCheckpoints151.Proof20
import InitECandidate.Proofs.WordStages.Pass151_3
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem checked : WordCse.wordCommonSubexpElim InitECandidate.Proofs.WordStages.pass151_3 = program14027 := by
  have h := congrArg Prod.snd node1334_eq
  rw [knowledge0_def] at h
  exact h
#print axioms checked
end InitECandidate.Proofs.CseCheckpoints151
