import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints64.Data
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints64
theorem node0_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_2_0 = (knowledge0, InitECandidate.Proofs.WordStages.word64_2_0) := by
  rw [knowledge0_def]
  kernel_rfl
theorem node1_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_63 = (knowledge1, InitECandidate.Proofs.WordStages.word64_4_63) := by
  rw [knowledge0_def, knowledge1_def]
  kernel_rfl
theorem node2_eq : WordCse.wordCse knowledge1 InitECandidate.Proofs.WordStages.word64_2_74 = (knowledge2, InitECandidate.Proofs.WordStages.word64_2_74) := by
  rw [knowledge1_def, knowledge2_def]
  kernel_rfl
theorem node3_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_65 = (knowledge2, InitECandidate.Proofs.WordStages.word64_4_65) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1_eq node2_eq
theorem node4_eq : WordCse.wordCse knowledge2 InitECandidate.Proofs.WordStages.word64_2_78 = (knowledge3, InitECandidate.Proofs.WordStages.word64_2_78) := by
  rw [knowledge2_def, knowledge3_def]
  kernel_rfl
theorem node5_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_69 = (knowledge3, InitECandidate.Proofs.WordStages.word64_4_69) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node3_eq node4_eq
theorem node6_eq : WordCse.wordCse knowledge3 InitECandidate.Proofs.WordStages.word64_2_86 = (knowledge4, InitECandidate.Proofs.WordStages.word64_4_76) := by
  rw [knowledge3_def, knowledge4_def]
  kernel_rfl
theorem node7_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_77 = (knowledge4, InitECandidate.Proofs.WordStages.word64_4_77) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node5_eq node6_eq
theorem node8_eq : WordCse.wordCse knowledge4 InitECandidate.Proofs.WordStages.word64_2_90 = (knowledge5, InitECandidate.Proofs.WordStages.word64_2_90) := by
  rw [knowledge4_def, knowledge5_def]
  kernel_rfl
theorem node9_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_79 = (knowledge5, InitECandidate.Proofs.WordStages.word64_4_79) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node7_eq node8_eq
theorem node10_eq : WordCse.wordCse knowledge5 InitECandidate.Proofs.WordStages.word64_2_94 = (knowledge6, InitECandidate.Proofs.WordStages.word64_2_94) := by
  rw [knowledge5_def, knowledge6_def]
  kernel_rfl
theorem node11_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_83 = (knowledge6, InitECandidate.Proofs.WordStages.word64_4_83) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node9_eq node10_eq
theorem node12_eq : WordCse.wordCse knowledge6 InitECandidate.Proofs.WordStages.word64_2_102 = (knowledge7, InitECandidate.Proofs.WordStages.word64_4_90) := by
  rw [knowledge6_def, knowledge7_def]
  kernel_rfl
theorem node13_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_91 = (knowledge7, InitECandidate.Proofs.WordStages.word64_4_91) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node11_eq node12_eq
theorem node14_eq : WordCse.wordCse knowledge7 InitECandidate.Proofs.WordStages.word64_2_106 = (knowledge8, InitECandidate.Proofs.WordStages.word64_2_106) := by
  rw [knowledge7_def, knowledge8_def]
  kernel_rfl
theorem node15_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_93 = (knowledge8, InitECandidate.Proofs.WordStages.word64_4_93) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node13_eq node14_eq
theorem node16_eq : WordCse.wordCse knowledge8 InitECandidate.Proofs.WordStages.word64_2_110 = (knowledge9, InitECandidate.Proofs.WordStages.word64_2_110) := by
  rw [knowledge8_def, knowledge9_def]
  kernel_rfl
theorem node17_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_97 = (knowledge9, InitECandidate.Proofs.WordStages.word64_4_97) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node15_eq node16_eq
theorem node18_eq : WordCse.wordCse knowledge9 InitECandidate.Proofs.WordStages.word64_2_118 = (knowledge10, InitECandidate.Proofs.WordStages.word64_4_104) := by
  rw [knowledge9_def, knowledge10_def]
  kernel_rfl
theorem node19_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_105 = (knowledge10, InitECandidate.Proofs.WordStages.word64_4_105) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node17_eq node18_eq
theorem node20_eq : WordCse.wordCse knowledge10 InitECandidate.Proofs.WordStages.word64_2_122 = (knowledge11, InitECandidate.Proofs.WordStages.word64_2_122) := by
  rw [knowledge10_def, knowledge11_def]
  kernel_rfl
theorem node21_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_107 = (knowledge11, InitECandidate.Proofs.WordStages.word64_4_107) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node19_eq node20_eq
theorem node22_eq : WordCse.wordCse knowledge11 InitECandidate.Proofs.WordStages.word64_2_126 = (knowledge12, InitECandidate.Proofs.WordStages.word64_2_126) := by
  rw [knowledge11_def, knowledge12_def]
  kernel_rfl
theorem node23_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_111 = (knowledge12, InitECandidate.Proofs.WordStages.word64_4_111) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node21_eq node22_eq
theorem node24_eq : WordCse.wordCse knowledge12 InitECandidate.Proofs.WordStages.word64_2_134 = (knowledge13, InitECandidate.Proofs.WordStages.word64_4_118) := by
  rw [knowledge12_def, knowledge13_def]
  kernel_rfl
theorem node25_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_119 = (knowledge13, InitECandidate.Proofs.WordStages.word64_4_119) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node23_eq node24_eq
theorem node26_eq : WordCse.wordCse knowledge13 InitECandidate.Proofs.WordStages.word64_2_138 = (knowledge14, InitECandidate.Proofs.WordStages.word64_2_138) := by
  rw [knowledge13_def, knowledge14_def]
  kernel_rfl
theorem node27_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_121 = (knowledge14, InitECandidate.Proofs.WordStages.word64_4_121) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node25_eq node26_eq
theorem node28_eq : WordCse.wordCse knowledge14 InitECandidate.Proofs.WordStages.word64_2_142 = (knowledge15, InitECandidate.Proofs.WordStages.word64_2_142) := by
  rw [knowledge14_def, knowledge15_def]
  kernel_rfl
theorem node29_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_125 = (knowledge15, InitECandidate.Proofs.WordStages.word64_4_125) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node27_eq node28_eq
theorem node30_eq : WordCse.wordCse knowledge15 InitECandidate.Proofs.WordStages.word64_2_150 = (knowledge16, InitECandidate.Proofs.WordStages.word64_4_132) := by
  rw [knowledge15_def, knowledge16_def]
  kernel_rfl
theorem node31_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_133 = (knowledge16, InitECandidate.Proofs.WordStages.word64_4_133) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node29_eq node30_eq
theorem node32_eq : WordCse.wordCse knowledge16 InitECandidate.Proofs.WordStages.word64_2_154 = (knowledge17, InitECandidate.Proofs.WordStages.word64_2_154) := by
  rw [knowledge16_def, knowledge17_def]
  kernel_rfl
theorem node33_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_135 = (knowledge17, InitECandidate.Proofs.WordStages.word64_4_135) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node31_eq node32_eq
theorem node34_eq : WordCse.wordCse knowledge17 InitECandidate.Proofs.WordStages.word64_2_158 = (knowledge18, InitECandidate.Proofs.WordStages.word64_2_158) := by
  rw [knowledge17_def, knowledge18_def]
  kernel_rfl
theorem node35_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_139 = (knowledge18, InitECandidate.Proofs.WordStages.word64_4_139) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node33_eq node34_eq
theorem node36_eq : WordCse.wordCse knowledge18 InitECandidate.Proofs.WordStages.word64_2_166 = (knowledge19, InitECandidate.Proofs.WordStages.word64_4_146) := by
  rw [knowledge18_def, knowledge19_def]
  kernel_rfl
theorem node37_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_147 = (knowledge19, InitECandidate.Proofs.WordStages.word64_4_147) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node35_eq node36_eq
theorem node38_eq : WordCse.wordCse knowledge19 InitECandidate.Proofs.WordStages.word64_2_170 = (knowledge20, InitECandidate.Proofs.WordStages.word64_2_170) := by
  rw [knowledge19_def, knowledge20_def]
  kernel_rfl
theorem node39_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_149 = (knowledge20, InitECandidate.Proofs.WordStages.word64_4_149) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node37_eq node38_eq
theorem node40_eq : WordCse.wordCse knowledge20 InitECandidate.Proofs.WordStages.word64_2_174 = (knowledge21, InitECandidate.Proofs.WordStages.word64_2_174) := by
  rw [knowledge20_def, knowledge21_def]
  kernel_rfl
theorem node41_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_153 = (knowledge21, InitECandidate.Proofs.WordStages.word64_4_153) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node39_eq node40_eq
theorem node42_eq : WordCse.wordCse knowledge21 InitECandidate.Proofs.WordStages.word64_2_182 = (knowledge22, InitECandidate.Proofs.WordStages.word64_4_160) := by
  rw [knowledge21_def, knowledge22_def]
  kernel_rfl
theorem node43_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_161 = (knowledge22, InitECandidate.Proofs.WordStages.word64_4_161) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node41_eq node42_eq
theorem node44_eq : WordCse.wordCse knowledge22 InitECandidate.Proofs.WordStages.word64_2_186 = (knowledge23, InitECandidate.Proofs.WordStages.word64_2_186) := by
  rw [knowledge22_def, knowledge23_def]
  kernel_rfl
theorem node45_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_163 = (knowledge23, InitECandidate.Proofs.WordStages.word64_4_163) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node43_eq node44_eq
theorem node46_eq : WordCse.wordCse knowledge23 InitECandidate.Proofs.WordStages.word64_2_190 = (knowledge24, InitECandidate.Proofs.WordStages.word64_2_190) := by
  rw [knowledge23_def, knowledge24_def]
  kernel_rfl
theorem node47_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_167 = (knowledge24, InitECandidate.Proofs.WordStages.word64_4_167) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node45_eq node46_eq
theorem node48_eq : WordCse.wordCse knowledge24 InitECandidate.Proofs.WordStages.word64_2_198 = (knowledge25, InitECandidate.Proofs.WordStages.word64_4_174) := by
  rw [knowledge24_def, knowledge25_def]
  kernel_rfl
theorem node49_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_175 = (knowledge25, InitECandidate.Proofs.WordStages.word64_4_175) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node47_eq node48_eq
theorem node50_eq : WordCse.wordCse knowledge25 InitECandidate.Proofs.WordStages.word64_2_202 = (knowledge26, InitECandidate.Proofs.WordStages.word64_2_202) := by
  rw [knowledge25_def, knowledge26_def]
  kernel_rfl
theorem node51_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_177 = (knowledge26, InitECandidate.Proofs.WordStages.word64_4_177) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node49_eq node50_eq
theorem node52_eq : WordCse.wordCse knowledge26 InitECandidate.Proofs.WordStages.word64_2_206 = (knowledge27, InitECandidate.Proofs.WordStages.word64_2_206) := by
  rw [knowledge26_def, knowledge27_def]
  kernel_rfl
theorem node53_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_181 = (knowledge27, InitECandidate.Proofs.WordStages.word64_4_181) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node51_eq node52_eq
theorem node54_eq : WordCse.wordCse knowledge27 InitECandidate.Proofs.WordStages.word64_2_214 = (knowledge28, InitECandidate.Proofs.WordStages.word64_4_188) := by
  rw [knowledge27_def, knowledge28_def]
  kernel_rfl
theorem node55_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_189 = (knowledge28, InitECandidate.Proofs.WordStages.word64_4_189) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node53_eq node54_eq
theorem node56_eq : WordCse.wordCse knowledge28 InitECandidate.Proofs.WordStages.word64_2_218 = (knowledge29, InitECandidate.Proofs.WordStages.word64_2_218) := by
  rw [knowledge28_def, knowledge29_def]
  kernel_rfl
theorem node57_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_191 = (knowledge29, InitECandidate.Proofs.WordStages.word64_4_191) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node55_eq node56_eq
theorem node58_eq : WordCse.wordCse knowledge29 InitECandidate.Proofs.WordStages.word64_2_222 = (knowledge30, InitECandidate.Proofs.WordStages.word64_2_222) := by
  rw [knowledge29_def, knowledge30_def]
  kernel_rfl
theorem node59_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_195 = (knowledge30, InitECandidate.Proofs.WordStages.word64_4_195) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node57_eq node58_eq
theorem node60_eq : WordCse.wordCse knowledge30 InitECandidate.Proofs.WordStages.word64_2_230 = (knowledge31, InitECandidate.Proofs.WordStages.word64_4_202) := by
  rw [knowledge30_def, knowledge31_def]
  kernel_rfl
theorem node61_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_203 = (knowledge31, InitECandidate.Proofs.WordStages.word64_4_203) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node59_eq node60_eq
theorem node62_eq : WordCse.wordCse knowledge31 InitECandidate.Proofs.WordStages.word64_2_234 = (knowledge32, InitECandidate.Proofs.WordStages.word64_2_234) := by
  rw [knowledge31_def, knowledge32_def]
  kernel_rfl
theorem node63_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_205 = (knowledge32, InitECandidate.Proofs.WordStages.word64_4_205) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node61_eq node62_eq
end InitECandidate.Proofs.CseCheckpoints64
