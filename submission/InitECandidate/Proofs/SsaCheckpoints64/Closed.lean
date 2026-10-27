import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof8
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem limit_eq : WordAlloc.limitVar InitECandidate.Proofs.WordStages.pass64_1 = 9 := by kernel_rfl
theorem setup_eq : WordAlloc.setupSSA (outputWidth := 64) 1 9 InitECandidate.Proofs.WordStages.pass64_1 = (InitECandidate.Proofs.WordStages.word64_2_0,state0,13) := by kernel_rfl
theorem checked : WordAlloc.fullSsaCcTrans 1 InitECandidate.Proofs.WordStages.pass64_1 = InitECandidate.Proofs.WordStages.pass64_2 := by
  rw [fullSsaStructural_eq]
  unfold fullSsaStructural
  rw [limit_eq]
  dsimp only
  rw [setup_eq]
  dsimp only
  have root_eq := node536_eq
  change ssaStructural InitECandidate.Proofs.WordStages.pass64_1 state0 13 [] = _ at root_eq
  rw [root_eq]
  kernel_rfl
#print axioms checked
end InitECandidate.Proofs.SsaCheckpoints64
