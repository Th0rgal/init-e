import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof31
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem limit_eq : WordAlloc.limitVar InitECandidate.Proofs.WordStages.pass154_1 = 197 := by kernel_rfl
theorem setup_eq : WordAlloc.setupSSA (outputWidth := 64) 64 197 InitECandidate.Proofs.WordStages.pass154_1 = (program47244,state64,453) := by kernel_rfl
theorem checked : WordAlloc.fullSsaCcTrans 64 InitECandidate.Proofs.WordStages.pass154_1 = InitECandidate.Proofs.WordStages.pass154_2 := by
  rw [fullSsaStructural_eq]
  unfold fullSsaStructural
  rw [limit_eq]
  dsimp only
  rw [setup_eq]
  dsimp only
  have root_eq := node2036_eq
  change ssaStructural InitECandidate.Proofs.WordStages.pass154_1 state64 453 [] = _ at root_eq
  rw [root_eq]
  kernel_rfl
#print axioms checked
end InitECandidate.Proofs.SsaCheckpoints154
