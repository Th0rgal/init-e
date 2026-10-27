import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof2
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node192_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_155 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_391,state392,701) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_155
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node190_eq, node191_eq]
  kernel_rfl
theorem node193_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state392 701 state1 = (InitECandidate.Proofs.WordStages.word64_2_392,state395,705) := by
  kernel_rfl
theorem node194_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_156 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_393,state395,705) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_156
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node192_eq, node193_eq]
  kernel_rfl
theorem node195_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state395 705 state1 = (InitECandidate.Proofs.WordStages.word64_2_394,state397,709) := by
  kernel_rfl
theorem node196_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_157 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_395,state397,709) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_157
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node194_eq, node195_eq]
  kernel_rfl
theorem node197_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state397 709 state1 = (InitECandidate.Proofs.WordStages.word64_2_398,state402,713) := by
  kernel_rfl
theorem node198_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_158 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_399,state402,713) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_158
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node196_eq, node197_eq]
  kernel_rfl
theorem node199_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_160 state402 713 state1 = (InitECandidate.Proofs.WordStages.word64_2_406,state408,729) := by
  kernel_rfl
theorem node200_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_161 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_407,state408,729) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_161
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node198_eq, node199_eq]
  kernel_rfl
theorem node201_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state408 729 state1 = (InitECandidate.Proofs.WordStages.word64_2_408,state411,733) := by
  kernel_rfl
theorem node202_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_162 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_409,state411,733) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_162
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node200_eq, node201_eq]
  kernel_rfl
theorem node203_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state411 733 state1 = (InitECandidate.Proofs.WordStages.word64_2_410,state413,737) := by
  kernel_rfl
theorem node204_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_163 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_411,state413,737) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_163
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node202_eq, node203_eq]
  kernel_rfl
theorem node205_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state413 737 state1 = (InitECandidate.Proofs.WordStages.word64_2_414,state418,741) := by
  kernel_rfl
theorem node206_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_164 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_415,state418,741) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_164
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node204_eq, node205_eq]
  kernel_rfl
theorem node207_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_166 state418 741 state1 = (InitECandidate.Proofs.WordStages.word64_2_422,state424,757) := by
  kernel_rfl
theorem node208_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_167 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_423,state424,757) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_167
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node206_eq, node207_eq]
  kernel_rfl
theorem node209_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state424 757 state1 = (InitECandidate.Proofs.WordStages.word64_2_424,state427,761) := by
  kernel_rfl
theorem node210_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_168 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_425,state427,761) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_168
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node208_eq, node209_eq]
  kernel_rfl
theorem node211_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state427 761 state1 = (InitECandidate.Proofs.WordStages.word64_2_426,state429,765) := by
  kernel_rfl
theorem node212_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_169 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_427,state429,765) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_169
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node210_eq, node211_eq]
  kernel_rfl
theorem node213_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state429 765 state1 = (InitECandidate.Proofs.WordStages.word64_2_430,state434,769) := by
  kernel_rfl
theorem node214_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_170 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_431,state434,769) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_170
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node212_eq, node213_eq]
  kernel_rfl
theorem node215_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_172 state434 769 state1 = (InitECandidate.Proofs.WordStages.word64_2_438,state440,785) := by
  kernel_rfl
theorem node216_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_173 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_439,state440,785) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_173
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node214_eq, node215_eq]
  kernel_rfl
theorem node217_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state440 785 state1 = (InitECandidate.Proofs.WordStages.word64_2_440,state443,789) := by
  kernel_rfl
theorem node218_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_174 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_441,state443,789) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_174
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node216_eq, node217_eq]
  kernel_rfl
theorem node219_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state443 789 state1 = (InitECandidate.Proofs.WordStages.word64_2_442,state445,793) := by
  kernel_rfl
theorem node220_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_175 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_443,state445,793) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_175
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node218_eq, node219_eq]
  kernel_rfl
theorem node221_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state445 793 state1 = (InitECandidate.Proofs.WordStages.word64_2_446,state450,797) := by
  kernel_rfl
theorem node222_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_176 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_447,state450,797) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_176
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node220_eq, node221_eq]
  kernel_rfl
theorem node223_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_178 state450 797 state1 = (InitECandidate.Proofs.WordStages.word64_2_454,state456,813) := by
  kernel_rfl
theorem node224_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_179 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_455,state456,813) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_179
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node222_eq, node223_eq]
  kernel_rfl
theorem node225_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state456 813 state1 = (InitECandidate.Proofs.WordStages.word64_2_456,state459,817) := by
  kernel_rfl
theorem node226_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_180 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_457,state459,817) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_180
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node224_eq, node225_eq]
  kernel_rfl
theorem node227_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state459 817 state1 = (InitECandidate.Proofs.WordStages.word64_2_458,state461,821) := by
  kernel_rfl
theorem node228_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_181 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_459,state461,821) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_181
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node226_eq, node227_eq]
  kernel_rfl
theorem node229_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state461 821 state1 = (InitECandidate.Proofs.WordStages.word64_2_462,state466,825) := by
  kernel_rfl
theorem node230_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_182 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_463,state466,825) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_182
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node228_eq, node229_eq]
  kernel_rfl
theorem node231_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_184 state466 825 state1 = (InitECandidate.Proofs.WordStages.word64_2_470,state472,841) := by
  kernel_rfl
theorem node232_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_185 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_471,state472,841) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_185
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node230_eq, node231_eq]
  kernel_rfl
theorem node233_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state472 841 state1 = (InitECandidate.Proofs.WordStages.word64_2_472,state475,845) := by
  kernel_rfl
theorem node234_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_186 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_473,state475,845) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_186
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node232_eq, node233_eq]
  kernel_rfl
theorem node235_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state475 845 state1 = (InitECandidate.Proofs.WordStages.word64_2_474,state477,849) := by
  kernel_rfl
theorem node236_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_187 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_475,state477,849) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_187
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node234_eq, node235_eq]
  kernel_rfl
theorem node237_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state477 849 state1 = (InitECandidate.Proofs.WordStages.word64_2_478,state482,853) := by
  kernel_rfl
theorem node238_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_188 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_479,state482,853) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_188
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node236_eq, node237_eq]
  kernel_rfl
theorem node239_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_190 state482 853 state1 = (InitECandidate.Proofs.WordStages.word64_2_486,state488,869) := by
  kernel_rfl
theorem node240_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_191 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_487,state488,869) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_191
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node238_eq, node239_eq]
  kernel_rfl
theorem node241_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state488 869 state1 = (InitECandidate.Proofs.WordStages.word64_2_488,state491,873) := by
  kernel_rfl
theorem node242_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_192 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_489,state491,873) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_192
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node240_eq, node241_eq]
  kernel_rfl
theorem node243_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state491 873 state1 = (InitECandidate.Proofs.WordStages.word64_2_490,state493,877) := by
  kernel_rfl
theorem node244_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_193 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_491,state493,877) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_193
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node242_eq, node243_eq]
  kernel_rfl
theorem node245_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state493 877 state1 = (InitECandidate.Proofs.WordStages.word64_2_494,state498,881) := by
  kernel_rfl
theorem node246_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_194 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_495,state498,881) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_194
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node244_eq, node245_eq]
  kernel_rfl
theorem node247_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_196 state498 881 state1 = (InitECandidate.Proofs.WordStages.word64_2_502,state504,897) := by
  kernel_rfl
theorem node248_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_197 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_503,state504,897) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_197
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node246_eq, node247_eq]
  kernel_rfl
theorem node249_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state504 897 state1 = (InitECandidate.Proofs.WordStages.word64_2_504,state507,901) := by
  kernel_rfl
theorem node250_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_198 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_505,state507,901) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_198
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node248_eq, node249_eq]
  kernel_rfl
theorem node251_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state507 901 state1 = (InitECandidate.Proofs.WordStages.word64_2_506,state509,905) := by
  kernel_rfl
theorem node252_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_199 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_507,state509,905) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_199
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node250_eq, node251_eq]
  kernel_rfl
theorem node253_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state509 905 state1 = (InitECandidate.Proofs.WordStages.word64_2_510,state514,909) := by
  kernel_rfl
theorem node254_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_200 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_511,state514,909) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_200
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node252_eq, node253_eq]
  kernel_rfl
theorem node255_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_202 state514 909 state1 = (InitECandidate.Proofs.WordStages.word64_2_518,state520,925) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
