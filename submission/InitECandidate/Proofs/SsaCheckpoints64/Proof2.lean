import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof1
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node128_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_107 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_263,state264,477) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_107
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node126_eq, node127_eq]
  kernel_rfl
theorem node129_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state264 477 state1 = (InitECandidate.Proofs.WordStages.word64_2_264,state267,481) := by
  kernel_rfl
theorem node130_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_108 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_265,state267,481) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_108
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node128_eq, node129_eq]
  kernel_rfl
theorem node131_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state267 481 state1 = (InitECandidate.Proofs.WordStages.word64_2_266,state269,485) := by
  kernel_rfl
theorem node132_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_109 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_267,state269,485) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_109
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node130_eq, node131_eq]
  kernel_rfl
theorem node133_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state269 485 state1 = (InitECandidate.Proofs.WordStages.word64_2_270,state274,489) := by
  kernel_rfl
theorem node134_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_110 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_271,state274,489) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_110
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node132_eq, node133_eq]
  kernel_rfl
theorem node135_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_112 state274 489 state1 = (InitECandidate.Proofs.WordStages.word64_2_278,state280,505) := by
  kernel_rfl
theorem node136_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_113 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_279,state280,505) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_113
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node134_eq, node135_eq]
  kernel_rfl
theorem node137_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state280 505 state1 = (InitECandidate.Proofs.WordStages.word64_2_280,state283,509) := by
  kernel_rfl
theorem node138_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_114 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_281,state283,509) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_114
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node136_eq, node137_eq]
  kernel_rfl
theorem node139_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state283 509 state1 = (InitECandidate.Proofs.WordStages.word64_2_282,state285,513) := by
  kernel_rfl
theorem node140_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_115 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_283,state285,513) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_115
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node138_eq, node139_eq]
  kernel_rfl
theorem node141_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state285 513 state1 = (InitECandidate.Proofs.WordStages.word64_2_286,state290,517) := by
  kernel_rfl
theorem node142_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_116 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_287,state290,517) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_116
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node140_eq, node141_eq]
  kernel_rfl
theorem node143_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_118 state290 517 state1 = (InitECandidate.Proofs.WordStages.word64_2_294,state296,533) := by
  kernel_rfl
theorem node144_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_119 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_295,state296,533) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_119
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node142_eq, node143_eq]
  kernel_rfl
theorem node145_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state296 533 state1 = (InitECandidate.Proofs.WordStages.word64_2_296,state299,537) := by
  kernel_rfl
theorem node146_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_120 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_297,state299,537) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_120
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node144_eq, node145_eq]
  kernel_rfl
theorem node147_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state299 537 state1 = (InitECandidate.Proofs.WordStages.word64_2_298,state301,541) := by
  kernel_rfl
theorem node148_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_121 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_299,state301,541) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_121
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node146_eq, node147_eq]
  kernel_rfl
theorem node149_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state301 541 state1 = (InitECandidate.Proofs.WordStages.word64_2_302,state306,545) := by
  kernel_rfl
theorem node150_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_122 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_303,state306,545) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_122
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node148_eq, node149_eq]
  kernel_rfl
theorem node151_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_124 state306 545 state1 = (InitECandidate.Proofs.WordStages.word64_2_310,state312,561) := by
  kernel_rfl
theorem node152_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_125 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_311,state312,561) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_125
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node150_eq, node151_eq]
  kernel_rfl
theorem node153_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state312 561 state1 = (InitECandidate.Proofs.WordStages.word64_2_312,state315,565) := by
  kernel_rfl
theorem node154_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_126 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_313,state315,565) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_126
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node152_eq, node153_eq]
  kernel_rfl
theorem node155_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state315 565 state1 = (InitECandidate.Proofs.WordStages.word64_2_314,state317,569) := by
  kernel_rfl
theorem node156_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_127 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_315,state317,569) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_127
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node154_eq, node155_eq]
  kernel_rfl
theorem node157_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state317 569 state1 = (InitECandidate.Proofs.WordStages.word64_2_318,state322,573) := by
  kernel_rfl
theorem node158_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_128 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_319,state322,573) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_128
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node156_eq, node157_eq]
  kernel_rfl
theorem node159_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_130 state322 573 state1 = (InitECandidate.Proofs.WordStages.word64_2_326,state328,589) := by
  kernel_rfl
theorem node160_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_131 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_327,state328,589) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_131
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node158_eq, node159_eq]
  kernel_rfl
theorem node161_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state328 589 state1 = (InitECandidate.Proofs.WordStages.word64_2_328,state331,593) := by
  kernel_rfl
theorem node162_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_132 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_329,state331,593) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_132
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node160_eq, node161_eq]
  kernel_rfl
theorem node163_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state331 593 state1 = (InitECandidate.Proofs.WordStages.word64_2_330,state333,597) := by
  kernel_rfl
theorem node164_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_133 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_331,state333,597) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_133
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node162_eq, node163_eq]
  kernel_rfl
theorem node165_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state333 597 state1 = (InitECandidate.Proofs.WordStages.word64_2_334,state338,601) := by
  kernel_rfl
theorem node166_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_134 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_335,state338,601) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_134
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node164_eq, node165_eq]
  kernel_rfl
theorem node167_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_136 state338 601 state1 = (InitECandidate.Proofs.WordStages.word64_2_342,state344,617) := by
  kernel_rfl
theorem node168_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_137 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_343,state344,617) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_137
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node166_eq, node167_eq]
  kernel_rfl
theorem node169_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state344 617 state1 = (InitECandidate.Proofs.WordStages.word64_2_344,state347,621) := by
  kernel_rfl
theorem node170_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_138 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_345,state347,621) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_138
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node168_eq, node169_eq]
  kernel_rfl
theorem node171_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state347 621 state1 = (InitECandidate.Proofs.WordStages.word64_2_346,state349,625) := by
  kernel_rfl
theorem node172_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_139 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_347,state349,625) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_139
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node170_eq, node171_eq]
  kernel_rfl
theorem node173_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state349 625 state1 = (InitECandidate.Proofs.WordStages.word64_2_350,state354,629) := by
  kernel_rfl
theorem node174_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_140 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_351,state354,629) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_140
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node172_eq, node173_eq]
  kernel_rfl
theorem node175_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_142 state354 629 state1 = (InitECandidate.Proofs.WordStages.word64_2_358,state360,645) := by
  kernel_rfl
theorem node176_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_143 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_359,state360,645) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_143
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node174_eq, node175_eq]
  kernel_rfl
theorem node177_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state360 645 state1 = (InitECandidate.Proofs.WordStages.word64_2_360,state363,649) := by
  kernel_rfl
theorem node178_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_144 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_361,state363,649) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_144
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node176_eq, node177_eq]
  kernel_rfl
theorem node179_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state363 649 state1 = (InitECandidate.Proofs.WordStages.word64_2_362,state365,653) := by
  kernel_rfl
theorem node180_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_145 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_363,state365,653) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_145
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node178_eq, node179_eq]
  kernel_rfl
theorem node181_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state365 653 state1 = (InitECandidate.Proofs.WordStages.word64_2_366,state370,657) := by
  kernel_rfl
theorem node182_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_146 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_367,state370,657) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_146
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node180_eq, node181_eq]
  kernel_rfl
theorem node183_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_148 state370 657 state1 = (InitECandidate.Proofs.WordStages.word64_2_374,state376,673) := by
  kernel_rfl
theorem node184_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_149 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_375,state376,673) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_149
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node182_eq, node183_eq]
  kernel_rfl
theorem node185_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state376 673 state1 = (InitECandidate.Proofs.WordStages.word64_2_376,state379,677) := by
  kernel_rfl
theorem node186_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_150 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_377,state379,677) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_150
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node184_eq, node185_eq]
  kernel_rfl
theorem node187_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state379 677 state1 = (InitECandidate.Proofs.WordStages.word64_2_378,state381,681) := by
  kernel_rfl
theorem node188_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_151 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_379,state381,681) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_151
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node186_eq, node187_eq]
  kernel_rfl
theorem node189_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state381 681 state1 = (InitECandidate.Proofs.WordStages.word64_2_382,state386,685) := by
  kernel_rfl
theorem node190_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_152 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_383,state386,685) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_152
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node188_eq, node189_eq]
  kernel_rfl
theorem node191_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_154 state386 685 state1 = (InitECandidate.Proofs.WordStages.word64_2_390,state392,701) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
