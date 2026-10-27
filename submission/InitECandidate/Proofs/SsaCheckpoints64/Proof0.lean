import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Data
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node0_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_6 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_7,state8,29) := by
  kernel_rfl
theorem node1_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state8 29 state1 = (InitECandidate.Proofs.WordStages.word64_2_8,state11,33) := by
  kernel_rfl
theorem node2_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_8 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_9,state11,33) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_8
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node0_eq, node1_eq]
  kernel_rfl
theorem node3_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state11 33 state1 = (InitECandidate.Proofs.WordStages.word64_2_10,state13,37) := by
  kernel_rfl
theorem node4_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_10 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_11,state13,37) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_10
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2_eq, node3_eq]
  kernel_rfl
theorem node5_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state13 37 state1 = (InitECandidate.Proofs.WordStages.word64_2_14,state18,41) := by
  kernel_rfl
theorem node6_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_14 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_15,state18,41) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_14
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node4_eq, node5_eq]
  kernel_rfl
theorem node7_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_16 state18 41 state1 = (InitECandidate.Proofs.WordStages.word64_2_22,state24,57) := by
  kernel_rfl
theorem node8_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_17 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_23,state24,57) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_17
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node6_eq, node7_eq]
  kernel_rfl
theorem node9_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state24 57 state1 = (InitECandidate.Proofs.WordStages.word64_2_24,state27,61) := by
  kernel_rfl
theorem node10_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_18 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_25,state27,61) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_18
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node8_eq, node9_eq]
  kernel_rfl
theorem node11_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state27 61 state1 = (InitECandidate.Proofs.WordStages.word64_2_26,state29,65) := by
  kernel_rfl
theorem node12_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_19 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_27,state29,65) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_19
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node10_eq, node11_eq]
  kernel_rfl
theorem node13_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state29 65 state1 = (InitECandidate.Proofs.WordStages.word64_2_30,state34,69) := by
  kernel_rfl
theorem node14_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_20 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_31,state34,69) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_20
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node12_eq, node13_eq]
  kernel_rfl
theorem node15_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_22 state34 69 state1 = (InitECandidate.Proofs.WordStages.word64_2_38,state40,85) := by
  kernel_rfl
theorem node16_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_23 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_39,state40,85) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_23
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node14_eq, node15_eq]
  kernel_rfl
theorem node17_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state40 85 state1 = (InitECandidate.Proofs.WordStages.word64_2_40,state43,89) := by
  kernel_rfl
theorem node18_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_24 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_41,state43,89) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_24
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node16_eq, node17_eq]
  kernel_rfl
theorem node19_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state43 89 state1 = (InitECandidate.Proofs.WordStages.word64_2_42,state45,93) := by
  kernel_rfl
theorem node20_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_25 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_43,state45,93) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_25
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node18_eq, node19_eq]
  kernel_rfl
theorem node21_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state45 93 state1 = (InitECandidate.Proofs.WordStages.word64_2_46,state50,97) := by
  kernel_rfl
theorem node22_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_26 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_47,state50,97) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_26
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node20_eq, node21_eq]
  kernel_rfl
theorem node23_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_28 state50 97 state1 = (InitECandidate.Proofs.WordStages.word64_2_54,state56,113) := by
  kernel_rfl
theorem node24_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_29 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_55,state56,113) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_29
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node22_eq, node23_eq]
  kernel_rfl
theorem node25_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state56 113 state1 = (InitECandidate.Proofs.WordStages.word64_2_56,state59,117) := by
  kernel_rfl
theorem node26_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_30 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_57,state59,117) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_30
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node24_eq, node25_eq]
  kernel_rfl
theorem node27_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state59 117 state1 = (InitECandidate.Proofs.WordStages.word64_2_58,state61,121) := by
  kernel_rfl
theorem node28_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_31 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_59,state61,121) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_31
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node26_eq, node27_eq]
  kernel_rfl
theorem node29_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state61 121 state1 = (InitECandidate.Proofs.WordStages.word64_2_62,state66,125) := by
  kernel_rfl
theorem node30_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_32 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_63,state66,125) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_32
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node28_eq, node29_eq]
  kernel_rfl
theorem node31_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_34 state66 125 state1 = (InitECandidate.Proofs.WordStages.word64_2_70,state72,141) := by
  kernel_rfl
theorem node32_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_35 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_71,state72,141) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_35
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node30_eq, node31_eq]
  kernel_rfl
theorem node33_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state72 141 state1 = (InitECandidate.Proofs.WordStages.word64_2_72,state75,145) := by
  kernel_rfl
theorem node34_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_36 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_73,state75,145) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_36
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node32_eq, node33_eq]
  kernel_rfl
theorem node35_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state75 145 state1 = (InitECandidate.Proofs.WordStages.word64_2_74,state77,149) := by
  kernel_rfl
theorem node36_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_37 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_75,state77,149) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_37
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node34_eq, node35_eq]
  kernel_rfl
theorem node37_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state77 149 state1 = (InitECandidate.Proofs.WordStages.word64_2_78,state82,153) := by
  kernel_rfl
theorem node38_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_38 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_79,state82,153) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_38
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node36_eq, node37_eq]
  kernel_rfl
theorem node39_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_40 state82 153 state1 = (InitECandidate.Proofs.WordStages.word64_2_86,state88,169) := by
  kernel_rfl
theorem node40_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_41 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_87,state88,169) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_41
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node38_eq, node39_eq]
  kernel_rfl
theorem node41_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state88 169 state1 = (InitECandidate.Proofs.WordStages.word64_2_88,state91,173) := by
  kernel_rfl
theorem node42_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_42 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_89,state91,173) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_42
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node40_eq, node41_eq]
  kernel_rfl
theorem node43_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state91 173 state1 = (InitECandidate.Proofs.WordStages.word64_2_90,state93,177) := by
  kernel_rfl
theorem node44_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_43 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_91,state93,177) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_43
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node42_eq, node43_eq]
  kernel_rfl
theorem node45_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state93 177 state1 = (InitECandidate.Proofs.WordStages.word64_2_94,state98,181) := by
  kernel_rfl
theorem node46_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_44 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_95,state98,181) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_44
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node44_eq, node45_eq]
  kernel_rfl
theorem node47_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_46 state98 181 state1 = (InitECandidate.Proofs.WordStages.word64_2_102,state104,197) := by
  kernel_rfl
theorem node48_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_47 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_103,state104,197) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_47
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node46_eq, node47_eq]
  kernel_rfl
theorem node49_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state104 197 state1 = (InitECandidate.Proofs.WordStages.word64_2_104,state107,201) := by
  kernel_rfl
theorem node50_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_48 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_105,state107,201) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_48
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node48_eq, node49_eq]
  kernel_rfl
theorem node51_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state107 201 state1 = (InitECandidate.Proofs.WordStages.word64_2_106,state109,205) := by
  kernel_rfl
theorem node52_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_49 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_107,state109,205) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_49
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node50_eq, node51_eq]
  kernel_rfl
theorem node53_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state109 205 state1 = (InitECandidate.Proofs.WordStages.word64_2_110,state114,209) := by
  kernel_rfl
theorem node54_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_50 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_111,state114,209) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_50
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node52_eq, node53_eq]
  kernel_rfl
theorem node55_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_52 state114 209 state1 = (InitECandidate.Proofs.WordStages.word64_2_118,state120,225) := by
  kernel_rfl
theorem node56_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_53 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_119,state120,225) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_53
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node54_eq, node55_eq]
  kernel_rfl
theorem node57_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state120 225 state1 = (InitECandidate.Proofs.WordStages.word64_2_120,state123,229) := by
  kernel_rfl
theorem node58_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_54 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_121,state123,229) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_54
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node56_eq, node57_eq]
  kernel_rfl
theorem node59_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state123 229 state1 = (InitECandidate.Proofs.WordStages.word64_2_122,state125,233) := by
  kernel_rfl
theorem node60_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_55 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_123,state125,233) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_55
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node58_eq, node59_eq]
  kernel_rfl
theorem node61_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state125 233 state1 = (InitECandidate.Proofs.WordStages.word64_2_126,state130,237) := by
  kernel_rfl
theorem node62_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_56 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_127,state130,237) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_56
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node60_eq, node61_eq]
  kernel_rfl
theorem node63_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_58 state130 237 state1 = (InitECandidate.Proofs.WordStages.word64_2_134,state136,253) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
