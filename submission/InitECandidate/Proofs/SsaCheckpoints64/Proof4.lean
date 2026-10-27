import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof3
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node256_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_203 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_519,state520,925) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_203
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node254_eq, node255_eq]
  kernel_rfl
theorem node257_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state520 925 state1 = (InitECandidate.Proofs.WordStages.word64_2_520,state523,929) := by
  kernel_rfl
theorem node258_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_204 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_521,state523,929) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_204
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node256_eq, node257_eq]
  kernel_rfl
theorem node259_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state523 929 state1 = (InitECandidate.Proofs.WordStages.word64_2_522,state525,933) := by
  kernel_rfl
theorem node260_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_205 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_523,state525,933) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_205
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node258_eq, node259_eq]
  kernel_rfl
theorem node261_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state525 933 state1 = (InitECandidate.Proofs.WordStages.word64_2_526,state530,937) := by
  kernel_rfl
theorem node262_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_206 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_527,state530,937) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_206
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node260_eq, node261_eq]
  kernel_rfl
theorem node263_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_208 state530 937 state1 = (InitECandidate.Proofs.WordStages.word64_2_534,state536,953) := by
  kernel_rfl
theorem node264_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_209 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_535,state536,953) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_209
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node262_eq, node263_eq]
  kernel_rfl
theorem node265_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state536 953 state1 = (InitECandidate.Proofs.WordStages.word64_2_536,state539,957) := by
  kernel_rfl
theorem node266_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_210 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_537,state539,957) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_210
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node264_eq, node265_eq]
  kernel_rfl
theorem node267_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state539 957 state1 = (InitECandidate.Proofs.WordStages.word64_2_538,state541,961) := by
  kernel_rfl
theorem node268_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_211 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_539,state541,961) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_211
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node266_eq, node267_eq]
  kernel_rfl
theorem node269_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state541 961 state1 = (InitECandidate.Proofs.WordStages.word64_2_542,state546,965) := by
  kernel_rfl
theorem node270_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_212 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_543,state546,965) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_212
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node268_eq, node269_eq]
  kernel_rfl
theorem node271_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_214 state546 965 state1 = (InitECandidate.Proofs.WordStages.word64_2_550,state552,981) := by
  kernel_rfl
theorem node272_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_215 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_551,state552,981) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_215
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node270_eq, node271_eq]
  kernel_rfl
theorem node273_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state552 981 state1 = (InitECandidate.Proofs.WordStages.word64_2_552,state555,985) := by
  kernel_rfl
theorem node274_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_216 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_553,state555,985) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_216
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node272_eq, node273_eq]
  kernel_rfl
theorem node275_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state555 985 state1 = (InitECandidate.Proofs.WordStages.word64_2_554,state557,989) := by
  kernel_rfl
theorem node276_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_217 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_555,state557,989) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_217
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node274_eq, node275_eq]
  kernel_rfl
theorem node277_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state557 989 state1 = (InitECandidate.Proofs.WordStages.word64_2_558,state562,993) := by
  kernel_rfl
theorem node278_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_218 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_559,state562,993) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_218
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node276_eq, node277_eq]
  kernel_rfl
theorem node279_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_220 state562 993 state1 = (InitECandidate.Proofs.WordStages.word64_2_566,state568,1009) := by
  kernel_rfl
theorem node280_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_221 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_567,state568,1009) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_221
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node278_eq, node279_eq]
  kernel_rfl
theorem node281_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state568 1009 state1 = (InitECandidate.Proofs.WordStages.word64_2_568,state571,1013) := by
  kernel_rfl
theorem node282_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_222 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_569,state571,1013) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_222
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node280_eq, node281_eq]
  kernel_rfl
theorem node283_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state571 1013 state1 = (InitECandidate.Proofs.WordStages.word64_2_570,state573,1017) := by
  kernel_rfl
theorem node284_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_223 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_571,state573,1017) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_223
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node282_eq, node283_eq]
  kernel_rfl
theorem node285_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state573 1017 state1 = (InitECandidate.Proofs.WordStages.word64_2_574,state578,1021) := by
  kernel_rfl
theorem node286_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_224 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_575,state578,1021) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_224
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node284_eq, node285_eq]
  kernel_rfl
theorem node287_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_226 state578 1021 state1 = (InitECandidate.Proofs.WordStages.word64_2_582,state584,1037) := by
  kernel_rfl
theorem node288_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_227 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_583,state584,1037) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_227
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node286_eq, node287_eq]
  kernel_rfl
theorem node289_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state584 1037 state1 = (InitECandidate.Proofs.WordStages.word64_2_584,state587,1041) := by
  kernel_rfl
theorem node290_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_228 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_585,state587,1041) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_228
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node288_eq, node289_eq]
  kernel_rfl
theorem node291_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state587 1041 state1 = (InitECandidate.Proofs.WordStages.word64_2_586,state589,1045) := by
  kernel_rfl
theorem node292_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_229 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_587,state589,1045) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_229
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node290_eq, node291_eq]
  kernel_rfl
theorem node293_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state589 1045 state1 = (InitECandidate.Proofs.WordStages.word64_2_590,state594,1049) := by
  kernel_rfl
theorem node294_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_230 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_591,state594,1049) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_230
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node292_eq, node293_eq]
  kernel_rfl
theorem node295_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_232 state594 1049 state1 = (InitECandidate.Proofs.WordStages.word64_2_598,state600,1065) := by
  kernel_rfl
theorem node296_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_233 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_599,state600,1065) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_233
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node294_eq, node295_eq]
  kernel_rfl
theorem node297_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state600 1065 state1 = (InitECandidate.Proofs.WordStages.word64_2_600,state603,1069) := by
  kernel_rfl
theorem node298_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_234 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_601,state603,1069) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_234
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node296_eq, node297_eq]
  kernel_rfl
theorem node299_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state603 1069 state1 = (InitECandidate.Proofs.WordStages.word64_2_602,state605,1073) := by
  kernel_rfl
theorem node300_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_235 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_603,state605,1073) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_235
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node298_eq, node299_eq]
  kernel_rfl
theorem node301_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state605 1073 state1 = (InitECandidate.Proofs.WordStages.word64_2_606,state610,1077) := by
  kernel_rfl
theorem node302_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_236 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_607,state610,1077) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_236
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node300_eq, node301_eq]
  kernel_rfl
theorem node303_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_238 state610 1077 state1 = (InitECandidate.Proofs.WordStages.word64_2_614,state616,1093) := by
  kernel_rfl
theorem node304_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_239 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_615,state616,1093) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_239
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node302_eq, node303_eq]
  kernel_rfl
theorem node305_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state616 1093 state1 = (InitECandidate.Proofs.WordStages.word64_2_616,state619,1097) := by
  kernel_rfl
theorem node306_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_240 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_617,state619,1097) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_240
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node304_eq, node305_eq]
  kernel_rfl
theorem node307_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state619 1097 state1 = (InitECandidate.Proofs.WordStages.word64_2_618,state621,1101) := by
  kernel_rfl
theorem node308_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_241 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_619,state621,1101) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_241
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node306_eq, node307_eq]
  kernel_rfl
theorem node309_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state621 1101 state1 = (InitECandidate.Proofs.WordStages.word64_2_622,state626,1105) := by
  kernel_rfl
theorem node310_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_242 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_623,state626,1105) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_242
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node308_eq, node309_eq]
  kernel_rfl
theorem node311_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_244 state626 1105 state1 = (InitECandidate.Proofs.WordStages.word64_2_630,state632,1121) := by
  kernel_rfl
theorem node312_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_245 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_631,state632,1121) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_245
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node310_eq, node311_eq]
  kernel_rfl
theorem node313_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state632 1121 state1 = (InitECandidate.Proofs.WordStages.word64_2_632,state635,1125) := by
  kernel_rfl
theorem node314_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_246 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_633,state635,1125) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_246
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node312_eq, node313_eq]
  kernel_rfl
theorem node315_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state635 1125 state1 = (InitECandidate.Proofs.WordStages.word64_2_634,state637,1129) := by
  kernel_rfl
theorem node316_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_247 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_635,state637,1129) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_247
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node314_eq, node315_eq]
  kernel_rfl
theorem node317_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state637 1129 state1 = (InitECandidate.Proofs.WordStages.word64_2_638,state642,1133) := by
  kernel_rfl
theorem node318_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_248 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_639,state642,1133) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_248
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node316_eq, node317_eq]
  kernel_rfl
theorem node319_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_250 state642 1133 state1 = (InitECandidate.Proofs.WordStages.word64_2_646,state648,1149) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
