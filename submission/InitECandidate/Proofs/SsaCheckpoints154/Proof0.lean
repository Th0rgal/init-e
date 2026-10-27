import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Data
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node0_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_55 state64 453 state65 = (program26124,state104,581) := by
  kernel_rfl
theorem node1_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_31 state104 581 state65 = (InitECandidate.Proofs.WordStages.word154_2_184,state110,585) := by
  kernel_rfl
theorem node2_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_57 state64 453 state65 = (program26125,state110,585) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_57
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node0_eq, node1_eq]
  kernel_rfl
theorem node3_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_71 state110 585 state65 = (program26143,state144,625) := by
  kernel_rfl
theorem node4_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_72 state64 453 state65 = (program26144,state144,625) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_72
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node2_eq, node3_eq]
  kernel_rfl
theorem node5_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_74 state144 625 state65 = (program26147,state158,633) := by
  kernel_rfl
theorem node6_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_75 state64 453 state65 = (program26148,state158,633) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_75
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node4_eq, node5_eq]
  kernel_rfl
theorem node7_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_37 state158 633 state65 = (program26149,state165,637) := by
  kernel_rfl
theorem node8_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_77 state64 453 state65 = (program26150,state165,637) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_77
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node6_eq, node7_eq]
  kernel_rfl
theorem node9_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_79 state165 637 state65 = (program26153,state180,645) := by
  kernel_rfl
theorem node10_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_80 state64 453 state65 = (program26154,state180,645) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_80
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node8_eq, node9_eq]
  kernel_rfl
theorem node11_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_41 state180 645 state65 = (program26155,state188,649) := by
  kernel_rfl
theorem node12_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_82 state64 453 state65 = (program26156,state188,649) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_82
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node10_eq, node11_eq]
  kernel_rfl
theorem node13_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_84 state188 649 state65 = (program26159,state199,657) := by
  kernel_rfl
theorem node14_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_85 state64 453 state65 = (program26160,state199,657) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_85
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node12_eq, node13_eq]
  kernel_rfl
theorem node15_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_45 state199 657 state65 = (InitECandidate.Proofs.WordStages.word154_2_222,state203,661) := by
  kernel_rfl
theorem node16_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_87 state64 453 state65 = (program26161,state203,661) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_87
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node14_eq, node15_eq]
  kernel_rfl
theorem node17_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_89 state203 661 state65 = (program26163,state217,669) := by
  kernel_rfl
theorem node18_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_90 state64 453 state65 = (program26164,state217,669) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_90
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node16_eq, node17_eq]
  kernel_rfl
theorem node19_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_49 state217 669 state65 = (InitECandidate.Proofs.WordStages.word154_2_228,state224,673) := by
  kernel_rfl
theorem node20_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_92 state64 453 state65 = (program26165,state224,673) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_92
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node18_eq, node19_eq]
  kernel_rfl
theorem node21_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_106 state224 673 state65 = (program26183,state254,713) := by
  kernel_rfl
theorem node22_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_107 state64 453 state65 = (program26184,state254,713) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_107
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node20_eq, node21_eq]
  kernel_rfl
theorem node23_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_109 state254 713 state65 = (program26187,state269,721) := by
  kernel_rfl
theorem node24_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_110 state64 453 state65 = (program26188,state269,721) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_110
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node22_eq, node23_eq]
  kernel_rfl
theorem node25_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_55 state269 721 state65 = (program26189,state277,725) := by
  kernel_rfl
theorem node26_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_112 state64 453 state65 = (program26190,state277,725) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_112
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node24_eq, node25_eq]
  kernel_rfl
theorem node27_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_114 state277 725 state65 = (program26193,state290,733) := by
  kernel_rfl
theorem node28_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_115 state64 453 state65 = (program26194,state290,733) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_115
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node26_eq, node27_eq]
  kernel_rfl
theorem node29_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_59 state290 733 state65 = (program26195,state296,737) := by
  kernel_rfl
theorem node30_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_117 state64 453 state65 = (program26196,state296,737) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_117
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node28_eq, node29_eq]
  kernel_rfl
theorem node31_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_119 state296 737 state65 = (program26199,state311,745) := by
  kernel_rfl
theorem node32_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_120 state64 453 state65 = (program26200,state311,745) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_120
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node30_eq, node31_eq]
  kernel_rfl
theorem node33_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_63 state311 745 state65 = (InitECandidate.Proofs.WordStages.word154_2_266,state319,749) := by
  kernel_rfl
theorem node34_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_122 state64 453 state65 = (program26201,state319,749) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_122
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node32_eq, node33_eq]
  kernel_rfl
theorem node35_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_124 state319 749 state65 = (program26203,state333,757) := by
  kernel_rfl
theorem node36_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_125 state64 453 state65 = (program26204,state333,757) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_125
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node34_eq, node35_eq]
  kernel_rfl
theorem node37_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_67 state333 757 state65 = (InitECandidate.Proofs.WordStages.word154_2_272,state340,761) := by
  kernel_rfl
theorem node38_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_127 state64 453 state65 = (program26205,state340,761) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_127
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node36_eq, node37_eq]
  kernel_rfl
theorem node39_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_141 state340 761 state65 = (program26223,state375,801) := by
  kernel_rfl
theorem node40_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_142 state64 453 state65 = (program26224,state375,801) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_142
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node38_eq, node39_eq]
  kernel_rfl
theorem node41_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_144 state375 801 state65 = (program26227,state387,809) := by
  kernel_rfl
theorem node42_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_145 state64 453 state65 = (program26228,state387,809) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_145
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node40_eq, node41_eq]
  kernel_rfl
theorem node43_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_73 state387 809 state65 = (program26229,state392,813) := by
  kernel_rfl
theorem node44_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_147 state64 453 state65 = (program26230,state392,813) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_147
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node42_eq, node43_eq]
  kernel_rfl
theorem node45_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_149 state392 813 state65 = (program26233,state406,821) := by
  kernel_rfl
theorem node46_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_150 state64 453 state65 = (program26234,state406,821) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_150
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node44_eq, node45_eq]
  kernel_rfl
theorem node47_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_77 state406 821 state65 = (program26235,state413,825) := by
  kernel_rfl
theorem node48_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_152 state64 453 state65 = (program26236,state413,825) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_152
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node46_eq, node47_eq]
  kernel_rfl
theorem node49_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_154 state413 825 state65 = (program26239,state427,833) := by
  kernel_rfl
theorem node50_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_155 state64 453 state65 = (program26240,state427,833) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_155
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node48_eq, node49_eq]
  kernel_rfl
theorem node51_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_81 state427 833 state65 = (InitECandidate.Proofs.WordStages.word154_2_310,state434,837) := by
  kernel_rfl
theorem node52_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_157 state64 453 state65 = (program26241,state434,837) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_157
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node50_eq, node51_eq]
  kernel_rfl
theorem node53_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_159 state434 837 state65 = (program26243,state449,845) := by
  kernel_rfl
theorem node54_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_160 state64 453 state65 = (program26244,state449,845) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_160
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node52_eq, node53_eq]
  kernel_rfl
theorem node55_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_85 state449 845 state65 = (InitECandidate.Proofs.WordStages.word154_2_316,state457,849) := by
  kernel_rfl
theorem node56_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_162 state64 453 state65 = (program26245,state457,849) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_162
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node54_eq, node55_eq]
  kernel_rfl
theorem node57_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_176 state457 849 state65 = (program26263,state489,889) := by
  kernel_rfl
theorem node58_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_177 state64 453 state65 = (program26264,state489,889) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_177
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node56_eq, node57_eq]
  kernel_rfl
theorem node59_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_179 state489 889 state65 = (program26267,state504,897) := by
  kernel_rfl
theorem node60_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_180 state64 453 state65 = (program26268,state504,897) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_180
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node58_eq, node59_eq]
  kernel_rfl
theorem node61_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_91 state504 897 state65 = (program26269,state512,901) := by
  kernel_rfl
theorem node62_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_182 state64 453 state65 = (program26270,state512,901) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_182
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node60_eq, node61_eq]
  kernel_rfl
theorem node63_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_184 state512 901 state65 = (program26273,state526,909) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
