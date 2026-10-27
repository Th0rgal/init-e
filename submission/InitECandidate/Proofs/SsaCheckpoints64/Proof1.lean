import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof0
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node64_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_59 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_135,state136,253) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_59
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node62_eq, node63_eq]
  kernel_rfl
theorem node65_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state136 253 state1 = (InitECandidate.Proofs.WordStages.word64_2_136,state139,257) := by
  kernel_rfl
theorem node66_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_60 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_137,state139,257) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_60
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node64_eq, node65_eq]
  kernel_rfl
theorem node67_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state139 257 state1 = (InitECandidate.Proofs.WordStages.word64_2_138,state141,261) := by
  kernel_rfl
theorem node68_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_61 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_139,state141,261) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_61
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node66_eq, node67_eq]
  kernel_rfl
theorem node69_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state141 261 state1 = (InitECandidate.Proofs.WordStages.word64_2_142,state146,265) := by
  kernel_rfl
theorem node70_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_62 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_143,state146,265) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_62
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node68_eq, node69_eq]
  kernel_rfl
theorem node71_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_64 state146 265 state1 = (InitECandidate.Proofs.WordStages.word64_2_150,state152,281) := by
  kernel_rfl
theorem node72_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_65 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_151,state152,281) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_65
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node70_eq, node71_eq]
  kernel_rfl
theorem node73_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state152 281 state1 = (InitECandidate.Proofs.WordStages.word64_2_152,state155,285) := by
  kernel_rfl
theorem node74_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_66 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_153,state155,285) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_66
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node72_eq, node73_eq]
  kernel_rfl
theorem node75_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state155 285 state1 = (InitECandidate.Proofs.WordStages.word64_2_154,state157,289) := by
  kernel_rfl
theorem node76_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_67 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_155,state157,289) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_67
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node74_eq, node75_eq]
  kernel_rfl
theorem node77_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state157 289 state1 = (InitECandidate.Proofs.WordStages.word64_2_158,state162,293) := by
  kernel_rfl
theorem node78_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_68 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_159,state162,293) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_68
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node76_eq, node77_eq]
  kernel_rfl
theorem node79_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_70 state162 293 state1 = (InitECandidate.Proofs.WordStages.word64_2_166,state168,309) := by
  kernel_rfl
theorem node80_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_71 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_167,state168,309) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_71
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node78_eq, node79_eq]
  kernel_rfl
theorem node81_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state168 309 state1 = (InitECandidate.Proofs.WordStages.word64_2_168,state171,313) := by
  kernel_rfl
theorem node82_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_72 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_169,state171,313) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_72
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node80_eq, node81_eq]
  kernel_rfl
theorem node83_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state171 313 state1 = (InitECandidate.Proofs.WordStages.word64_2_170,state173,317) := by
  kernel_rfl
theorem node84_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_73 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_171,state173,317) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_73
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node82_eq, node83_eq]
  kernel_rfl
theorem node85_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state173 317 state1 = (InitECandidate.Proofs.WordStages.word64_2_174,state178,321) := by
  kernel_rfl
theorem node86_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_74 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_175,state178,321) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_74
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node84_eq, node85_eq]
  kernel_rfl
theorem node87_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_76 state178 321 state1 = (InitECandidate.Proofs.WordStages.word64_2_182,state184,337) := by
  kernel_rfl
theorem node88_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_77 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_183,state184,337) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_77
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node86_eq, node87_eq]
  kernel_rfl
theorem node89_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state184 337 state1 = (InitECandidate.Proofs.WordStages.word64_2_184,state187,341) := by
  kernel_rfl
theorem node90_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_78 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_185,state187,341) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_78
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node88_eq, node89_eq]
  kernel_rfl
theorem node91_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state187 341 state1 = (InitECandidate.Proofs.WordStages.word64_2_186,state189,345) := by
  kernel_rfl
theorem node92_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_79 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_187,state189,345) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_79
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node90_eq, node91_eq]
  kernel_rfl
theorem node93_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state189 345 state1 = (InitECandidate.Proofs.WordStages.word64_2_190,state194,349) := by
  kernel_rfl
theorem node94_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_80 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_191,state194,349) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_80
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node92_eq, node93_eq]
  kernel_rfl
theorem node95_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_82 state194 349 state1 = (InitECandidate.Proofs.WordStages.word64_2_198,state200,365) := by
  kernel_rfl
theorem node96_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_83 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_199,state200,365) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_83
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node94_eq, node95_eq]
  kernel_rfl
theorem node97_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state200 365 state1 = (InitECandidate.Proofs.WordStages.word64_2_200,state203,369) := by
  kernel_rfl
theorem node98_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_84 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_201,state203,369) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_84
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node96_eq, node97_eq]
  kernel_rfl
theorem node99_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state203 369 state1 = (InitECandidate.Proofs.WordStages.word64_2_202,state205,373) := by
  kernel_rfl
theorem node100_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_85 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_203,state205,373) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_85
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node98_eq, node99_eq]
  kernel_rfl
theorem node101_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state205 373 state1 = (InitECandidate.Proofs.WordStages.word64_2_206,state210,377) := by
  kernel_rfl
theorem node102_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_86 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_207,state210,377) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_86
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node100_eq, node101_eq]
  kernel_rfl
theorem node103_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_88 state210 377 state1 = (InitECandidate.Proofs.WordStages.word64_2_214,state216,393) := by
  kernel_rfl
theorem node104_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_89 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_215,state216,393) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_89
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node102_eq, node103_eq]
  kernel_rfl
theorem node105_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state216 393 state1 = (InitECandidate.Proofs.WordStages.word64_2_216,state219,397) := by
  kernel_rfl
theorem node106_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_90 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_217,state219,397) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_90
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node104_eq, node105_eq]
  kernel_rfl
theorem node107_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state219 397 state1 = (InitECandidate.Proofs.WordStages.word64_2_218,state221,401) := by
  kernel_rfl
theorem node108_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_91 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_219,state221,401) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_91
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node106_eq, node107_eq]
  kernel_rfl
theorem node109_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state221 401 state1 = (InitECandidate.Proofs.WordStages.word64_2_222,state226,405) := by
  kernel_rfl
theorem node110_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_92 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_223,state226,405) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_92
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node108_eq, node109_eq]
  kernel_rfl
theorem node111_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_94 state226 405 state1 = (InitECandidate.Proofs.WordStages.word64_2_230,state232,421) := by
  kernel_rfl
theorem node112_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_95 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_231,state232,421) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_95
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node110_eq, node111_eq]
  kernel_rfl
theorem node113_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state232 421 state1 = (InitECandidate.Proofs.WordStages.word64_2_232,state235,425) := by
  kernel_rfl
theorem node114_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_96 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_233,state235,425) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_96
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node112_eq, node113_eq]
  kernel_rfl
theorem node115_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state235 425 state1 = (InitECandidate.Proofs.WordStages.word64_2_234,state237,429) := by
  kernel_rfl
theorem node116_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_97 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_235,state237,429) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_97
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node114_eq, node115_eq]
  kernel_rfl
theorem node117_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state237 429 state1 = (InitECandidate.Proofs.WordStages.word64_2_238,state242,433) := by
  kernel_rfl
theorem node118_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_98 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_239,state242,433) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_98
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node116_eq, node117_eq]
  kernel_rfl
theorem node119_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_100 state242 433 state1 = (InitECandidate.Proofs.WordStages.word64_2_246,state248,449) := by
  kernel_rfl
theorem node120_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_101 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_247,state248,449) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_101
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node118_eq, node119_eq]
  kernel_rfl
theorem node121_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state248 449 state1 = (InitECandidate.Proofs.WordStages.word64_2_248,state251,453) := by
  kernel_rfl
theorem node122_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_102 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_249,state251,453) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_102
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node120_eq, node121_eq]
  kernel_rfl
theorem node123_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state251 453 state1 = (InitECandidate.Proofs.WordStages.word64_2_250,state253,457) := by
  kernel_rfl
theorem node124_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_103 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_251,state253,457) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_103
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node122_eq, node123_eq]
  kernel_rfl
theorem node125_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state253 457 state1 = (InitECandidate.Proofs.WordStages.word64_2_254,state258,461) := by
  kernel_rfl
theorem node126_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_104 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_255,state258,461) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_104
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node124_eq, node125_eq]
  kernel_rfl
theorem node127_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_106 state258 461 state1 = (InitECandidate.Proofs.WordStages.word64_2_262,state264,477) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
