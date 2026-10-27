import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof7
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node512_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_395 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1031,state1032,1821) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_395
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node510_eq, node511_eq]
  kernel_rfl
theorem node513_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state1032 1821 state1 = (InitECandidate.Proofs.WordStages.word64_2_1032,state1035,1825) := by
  kernel_rfl
theorem node514_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_396 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1033,state1035,1825) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_396
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node512_eq, node513_eq]
  kernel_rfl
theorem node515_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state1035 1825 state1 = (InitECandidate.Proofs.WordStages.word64_2_1034,state1037,1829) := by
  kernel_rfl
theorem node516_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_397 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1035,state1037,1829) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_397
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node514_eq, node515_eq]
  kernel_rfl
theorem node517_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state1037 1829 state1 = (InitECandidate.Proofs.WordStages.word64_2_1038,state1042,1833) := by
  kernel_rfl
theorem node518_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_398 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1039,state1042,1833) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_398
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node516_eq, node517_eq]
  kernel_rfl
theorem node519_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_400 state1042 1833 state1 = (InitECandidate.Proofs.WordStages.word64_2_1046,state1048,1849) := by
  kernel_rfl
theorem node520_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_401 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1047,state1048,1849) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_401
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node518_eq, node519_eq]
  kernel_rfl
theorem node521_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state1048 1849 state1 = (InitECandidate.Proofs.WordStages.word64_2_1048,state1051,1853) := by
  kernel_rfl
theorem node522_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_402 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1049,state1051,1853) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_402
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node520_eq, node521_eq]
  kernel_rfl
theorem node523_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state1051 1853 state1 = (InitECandidate.Proofs.WordStages.word64_2_1050,state1053,1857) := by
  kernel_rfl
theorem node524_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_403 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1051,state1053,1857) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_403
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node522_eq, node523_eq]
  kernel_rfl
theorem node525_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state1053 1857 state1 = (InitECandidate.Proofs.WordStages.word64_2_1054,state1058,1861) := by
  kernel_rfl
theorem node526_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_404 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1055,state1058,1861) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_404
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node524_eq, node525_eq]
  kernel_rfl
theorem node527_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_406 state1058 1861 state1 = (InitECandidate.Proofs.WordStages.word64_2_1062,state1064,1877) := by
  kernel_rfl
theorem node528_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_407 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1063,state1064,1877) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_407
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node526_eq, node527_eq]
  kernel_rfl
theorem node529_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state1064 1877 state1 = (InitECandidate.Proofs.WordStages.word64_2_1064,state1067,1881) := by
  kernel_rfl
theorem node530_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_408 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1065,state1067,1881) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_408
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node528_eq, node529_eq]
  kernel_rfl
theorem node531_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state1067 1881 state1 = (InitECandidate.Proofs.WordStages.word64_2_1066,state1069,1885) := by
  kernel_rfl
theorem node532_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_409 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1067,state1069,1885) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_409
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node530_eq, node531_eq]
  kernel_rfl
theorem node533_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state1069 1885 state1 = (InitECandidate.Proofs.WordStages.word64_2_1070,state1074,1889) := by
  kernel_rfl
theorem node534_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_410 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1071,state1074,1889) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_410
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node532_eq, node533_eq]
  kernel_rfl
theorem node535_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_0_337 state1074 1889 state1 = (InitECandidate.Proofs.WordStages.word64_2_1074,state1074,1889) := by
  kernel_rfl
theorem node536_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_412 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1075,state1074,1889) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_412
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node534_eq, node535_eq]
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
