import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Data
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node0_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_0 = (knowledge0, InitECandidate.Proofs.WordStages.word151_2_0) := by
  rw [knowledge0_def]
  kernel_rfl
theorem node1_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_63 = (knowledge1, InitECandidate.Proofs.WordStages.word151_2_63) := by
  rw [knowledge0_def, knowledge1_def]
  kernel_rfl
theorem node2_eq : WordCse.wordCse knowledge1 InitECandidate.Proofs.WordStages.word151_2_64 = (knowledge2, InitECandidate.Proofs.WordStages.word151_2_64) := by
  rw [knowledge1_def, knowledge2_def]
  kernel_rfl
theorem node3_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_65 = (knowledge2, InitECandidate.Proofs.WordStages.word151_2_65) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1_eq node2_eq
theorem node4_eq : WordCse.wordCse knowledge2 InitECandidate.Proofs.WordStages.word151_2_84 = (knowledge3, InitECandidate.Proofs.WordStages.word151_2_84) := by
  rw [knowledge2_def, knowledge3_def]
  kernel_rfl
theorem node5_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_85 = (knowledge3, InitECandidate.Proofs.WordStages.word151_2_85) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node3_eq node4_eq
theorem node6_eq : WordCse.wordCse knowledge3 InitECandidate.Proofs.WordStages.word151_2_88 = (knowledge4, InitECandidate.Proofs.WordStages.word151_2_88) := by
  rw [knowledge3_def, knowledge4_def]
  kernel_rfl
theorem node7_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_89 = (knowledge4, InitECandidate.Proofs.WordStages.word151_2_89) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node5_eq node6_eq
theorem node8_eq : WordCse.wordCse knowledge4 InitECandidate.Proofs.WordStages.word151_2_90 = (knowledge5, InitECandidate.Proofs.WordStages.word151_2_90) := by
  rw [knowledge4_def, knowledge5_def]
  kernel_rfl
theorem node9_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_91 = (knowledge5, InitECandidate.Proofs.WordStages.word151_2_91) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node7_eq node8_eq
theorem node10_eq : WordCse.wordCse knowledge5 InitECandidate.Proofs.WordStages.word151_2_94 = (knowledge6, InitECandidate.Proofs.WordStages.word151_2_94) := by
  rw [knowledge5_def, knowledge6_def]
  kernel_rfl
theorem node11_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_95 = (knowledge6, InitECandidate.Proofs.WordStages.word151_2_95) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node9_eq node10_eq
theorem node12_eq : WordCse.wordCse knowledge6 InitECandidate.Proofs.WordStages.word151_2_96 = (knowledge7, InitECandidate.Proofs.WordStages.word151_2_96) := by
  rw [knowledge6_def, knowledge7_def]
  kernel_rfl
theorem node13_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_97 = (knowledge7, InitECandidate.Proofs.WordStages.word151_2_97) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node11_eq node12_eq
theorem node14_eq : WordCse.wordCse knowledge7 InitECandidate.Proofs.WordStages.word151_2_100 = (knowledge8, InitECandidate.Proofs.WordStages.word151_2_100) := by
  rw [knowledge7_def, knowledge8_def]
  kernel_rfl
theorem node15_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_101 = (knowledge8, InitECandidate.Proofs.WordStages.word151_2_101) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node13_eq node14_eq
theorem node16_eq : WordCse.wordCse knowledge8 InitECandidate.Proofs.WordStages.word151_2_102 = (knowledge9, InitECandidate.Proofs.WordStages.word151_2_102) := by
  rw [knowledge8_def, knowledge9_def]
  kernel_rfl
theorem node17_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_103 = (knowledge9, InitECandidate.Proofs.WordStages.word151_2_103) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node15_eq node16_eq
theorem node18_eq : WordCse.wordCse knowledge9 InitECandidate.Proofs.WordStages.word151_2_106 = (knowledge10, InitECandidate.Proofs.WordStages.word151_2_106) := by
  rw [knowledge9_def, knowledge10_def]
  kernel_rfl
theorem node19_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_107 = (knowledge10, InitECandidate.Proofs.WordStages.word151_2_107) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node17_eq node18_eq
theorem node20_eq : WordCse.wordCse knowledge10 InitECandidate.Proofs.WordStages.word151_2_108 = (knowledge11, InitECandidate.Proofs.WordStages.word151_2_108) := by
  rw [knowledge10_def, knowledge11_def]
  kernel_rfl
theorem node21_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_109 = (knowledge11, InitECandidate.Proofs.WordStages.word151_2_109) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node19_eq node20_eq
theorem node22_eq : WordCse.wordCse knowledge11 InitECandidate.Proofs.WordStages.word151_2_128 = (knowledge12, InitECandidate.Proofs.WordStages.word151_2_128) := by
  rw [knowledge11_def, knowledge12_def]
  kernel_rfl
theorem node23_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_129 = (knowledge12, InitECandidate.Proofs.WordStages.word151_2_129) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node21_eq node22_eq
theorem node24_eq : WordCse.wordCse knowledge12 InitECandidate.Proofs.WordStages.word151_2_132 = (knowledge13, InitECandidate.Proofs.WordStages.word151_2_132) := by
  rw [knowledge12_def, knowledge13_def]
  kernel_rfl
theorem node25_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_133 = (knowledge13, InitECandidate.Proofs.WordStages.word151_2_133) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node23_eq node24_eq
theorem node26_eq : WordCse.wordCse knowledge13 InitECandidate.Proofs.WordStages.word151_2_134 = (knowledge14, InitECandidate.Proofs.WordStages.word151_2_134) := by
  rw [knowledge13_def, knowledge14_def]
  kernel_rfl
theorem node27_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_135 = (knowledge14, InitECandidate.Proofs.WordStages.word151_2_135) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node25_eq node26_eq
theorem node28_eq : WordCse.wordCse knowledge14 InitECandidate.Proofs.WordStages.word151_2_138 = (knowledge15, InitECandidate.Proofs.WordStages.word151_2_138) := by
  rw [knowledge14_def, knowledge15_def]
  kernel_rfl
theorem node29_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_139 = (knowledge15, InitECandidate.Proofs.WordStages.word151_2_139) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node27_eq node28_eq
theorem node30_eq : WordCse.wordCse knowledge15 InitECandidate.Proofs.WordStages.word151_2_140 = (knowledge16, InitECandidate.Proofs.WordStages.word151_2_140) := by
  rw [knowledge15_def, knowledge16_def]
  kernel_rfl
theorem node31_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_141 = (knowledge16, InitECandidate.Proofs.WordStages.word151_2_141) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node29_eq node30_eq
theorem node32_eq : WordCse.wordCse knowledge16 InitECandidate.Proofs.WordStages.word151_2_144 = (knowledge17, InitECandidate.Proofs.WordStages.word151_2_144) := by
  rw [knowledge16_def, knowledge17_def]
  kernel_rfl
theorem node33_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_145 = (knowledge17, InitECandidate.Proofs.WordStages.word151_2_145) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node31_eq node32_eq
theorem node34_eq : WordCse.wordCse knowledge17 InitECandidate.Proofs.WordStages.word151_2_146 = (knowledge18, InitECandidate.Proofs.WordStages.word151_2_146) := by
  rw [knowledge17_def, knowledge18_def]
  kernel_rfl
theorem node35_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_147 = (knowledge18, InitECandidate.Proofs.WordStages.word151_2_147) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node33_eq node34_eq
theorem node36_eq : WordCse.wordCse knowledge18 InitECandidate.Proofs.WordStages.word151_2_150 = (knowledge19, InitECandidate.Proofs.WordStages.word151_2_150) := by
  rw [knowledge18_def, knowledge19_def]
  kernel_rfl
theorem node37_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_151 = (knowledge19, InitECandidate.Proofs.WordStages.word151_2_151) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node35_eq node36_eq
theorem node38_eq : WordCse.wordCse knowledge19 InitECandidate.Proofs.WordStages.word151_2_152 = (knowledge20, InitECandidate.Proofs.WordStages.word151_2_152) := by
  rw [knowledge19_def, knowledge20_def]
  kernel_rfl
theorem node39_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_153 = (knowledge20, InitECandidate.Proofs.WordStages.word151_2_153) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node37_eq node38_eq
theorem node40_eq : WordCse.wordCse knowledge20 InitECandidate.Proofs.WordStages.word151_2_172 = (knowledge21, InitECandidate.Proofs.WordStages.word151_2_172) := by
  rw [knowledge20_def, knowledge21_def]
  kernel_rfl
theorem node41_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_173 = (knowledge21, InitECandidate.Proofs.WordStages.word151_2_173) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node39_eq node40_eq
theorem node42_eq : WordCse.wordCse knowledge21 InitECandidate.Proofs.WordStages.word151_2_176 = (knowledge22, InitECandidate.Proofs.WordStages.word151_2_176) := by
  rw [knowledge21_def, knowledge22_def]
  kernel_rfl
theorem node43_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_177 = (knowledge22, InitECandidate.Proofs.WordStages.word151_2_177) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node41_eq node42_eq
theorem node44_eq : WordCse.wordCse knowledge22 InitECandidate.Proofs.WordStages.word151_2_178 = (knowledge23, InitECandidate.Proofs.WordStages.word151_2_178) := by
  rw [knowledge22_def, knowledge23_def]
  kernel_rfl
theorem node45_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_179 = (knowledge23, InitECandidate.Proofs.WordStages.word151_2_179) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node43_eq node44_eq
theorem node46_eq : WordCse.wordCse knowledge23 InitECandidate.Proofs.WordStages.word151_2_182 = (knowledge24, InitECandidate.Proofs.WordStages.word151_2_182) := by
  rw [knowledge23_def, knowledge24_def]
  kernel_rfl
theorem node47_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_183 = (knowledge24, InitECandidate.Proofs.WordStages.word151_2_183) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node45_eq node46_eq
theorem node48_eq : WordCse.wordCse knowledge24 InitECandidate.Proofs.WordStages.word151_2_184 = (knowledge25, InitECandidate.Proofs.WordStages.word151_2_184) := by
  rw [knowledge24_def, knowledge25_def]
  kernel_rfl
theorem node49_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_185 = (knowledge25, InitECandidate.Proofs.WordStages.word151_2_185) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node47_eq node48_eq
theorem node50_eq : WordCse.wordCse knowledge25 InitECandidate.Proofs.WordStages.word151_2_188 = (knowledge26, InitECandidate.Proofs.WordStages.word151_2_188) := by
  rw [knowledge25_def, knowledge26_def]
  kernel_rfl
theorem node51_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_189 = (knowledge26, InitECandidate.Proofs.WordStages.word151_2_189) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node49_eq node50_eq
theorem node52_eq : WordCse.wordCse knowledge26 InitECandidate.Proofs.WordStages.word151_2_190 = (knowledge27, InitECandidate.Proofs.WordStages.word151_2_190) := by
  rw [knowledge26_def, knowledge27_def]
  kernel_rfl
theorem node53_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_191 = (knowledge27, InitECandidate.Proofs.WordStages.word151_2_191) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node51_eq node52_eq
theorem node54_eq : WordCse.wordCse knowledge27 InitECandidate.Proofs.WordStages.word151_2_194 = (knowledge28, InitECandidate.Proofs.WordStages.word151_2_194) := by
  rw [knowledge27_def, knowledge28_def]
  kernel_rfl
theorem node55_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_195 = (knowledge28, InitECandidate.Proofs.WordStages.word151_2_195) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node53_eq node54_eq
theorem node56_eq : WordCse.wordCse knowledge28 InitECandidate.Proofs.WordStages.word151_2_196 = (knowledge29, InitECandidate.Proofs.WordStages.word151_2_196) := by
  rw [knowledge28_def, knowledge29_def]
  kernel_rfl
theorem node57_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_197 = (knowledge29, InitECandidate.Proofs.WordStages.word151_2_197) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node55_eq node56_eq
theorem node58_eq : WordCse.wordCse knowledge29 InitECandidate.Proofs.WordStages.word151_2_216 = (knowledge30, InitECandidate.Proofs.WordStages.word151_2_216) := by
  rw [knowledge29_def, knowledge30_def]
  kernel_rfl
theorem node59_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_217 = (knowledge30, InitECandidate.Proofs.WordStages.word151_2_217) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node57_eq node58_eq
theorem node60_eq : WordCse.wordCse knowledge30 InitECandidate.Proofs.WordStages.word151_2_220 = (knowledge31, InitECandidate.Proofs.WordStages.word151_2_220) := by
  rw [knowledge30_def, knowledge31_def]
  kernel_rfl
theorem node61_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_221 = (knowledge31, InitECandidate.Proofs.WordStages.word151_2_221) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node59_eq node60_eq
theorem node62_eq : WordCse.wordCse knowledge31 InitECandidate.Proofs.WordStages.word151_2_222 = (knowledge32, InitECandidate.Proofs.WordStages.word151_2_222) := by
  rw [knowledge31_def, knowledge32_def]
  kernel_rfl
theorem node63_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_223 = (knowledge32, InitECandidate.Proofs.WordStages.word151_2_223) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node61_eq node62_eq
end InitECandidate.Proofs.CseCheckpoints151
