import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof4
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node320_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_251 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_647,state648,1149) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_251
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node318_eq, node319_eq]
  kernel_rfl
theorem node321_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state648 1149 state1 = (InitECandidate.Proofs.WordStages.word64_2_648,state651,1153) := by
  kernel_rfl
theorem node322_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_252 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_649,state651,1153) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_252
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node320_eq, node321_eq]
  kernel_rfl
theorem node323_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state651 1153 state1 = (InitECandidate.Proofs.WordStages.word64_2_650,state653,1157) := by
  kernel_rfl
theorem node324_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_253 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_651,state653,1157) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_253
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node322_eq, node323_eq]
  kernel_rfl
theorem node325_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state653 1157 state1 = (InitECandidate.Proofs.WordStages.word64_2_654,state658,1161) := by
  kernel_rfl
theorem node326_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_254 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_655,state658,1161) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_254
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node324_eq, node325_eq]
  kernel_rfl
theorem node327_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_256 state658 1161 state1 = (InitECandidate.Proofs.WordStages.word64_2_662,state664,1177) := by
  kernel_rfl
theorem node328_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_257 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_663,state664,1177) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_257
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node326_eq, node327_eq]
  kernel_rfl
theorem node329_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state664 1177 state1 = (InitECandidate.Proofs.WordStages.word64_2_664,state667,1181) := by
  kernel_rfl
theorem node330_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_258 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_665,state667,1181) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_258
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node328_eq, node329_eq]
  kernel_rfl
theorem node331_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state667 1181 state1 = (InitECandidate.Proofs.WordStages.word64_2_666,state669,1185) := by
  kernel_rfl
theorem node332_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_259 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_667,state669,1185) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_259
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node330_eq, node331_eq]
  kernel_rfl
theorem node333_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state669 1185 state1 = (InitECandidate.Proofs.WordStages.word64_2_670,state674,1189) := by
  kernel_rfl
theorem node334_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_260 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_671,state674,1189) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_260
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node332_eq, node333_eq]
  kernel_rfl
theorem node335_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_262 state674 1189 state1 = (InitECandidate.Proofs.WordStages.word64_2_678,state680,1205) := by
  kernel_rfl
theorem node336_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_263 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_679,state680,1205) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_263
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node334_eq, node335_eq]
  kernel_rfl
theorem node337_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state680 1205 state1 = (InitECandidate.Proofs.WordStages.word64_2_680,state683,1209) := by
  kernel_rfl
theorem node338_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_264 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_681,state683,1209) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_264
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node336_eq, node337_eq]
  kernel_rfl
theorem node339_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state683 1209 state1 = (InitECandidate.Proofs.WordStages.word64_2_682,state685,1213) := by
  kernel_rfl
theorem node340_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_265 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_683,state685,1213) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_265
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node338_eq, node339_eq]
  kernel_rfl
theorem node341_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state685 1213 state1 = (InitECandidate.Proofs.WordStages.word64_2_686,state690,1217) := by
  kernel_rfl
theorem node342_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_266 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_687,state690,1217) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_266
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node340_eq, node341_eq]
  kernel_rfl
theorem node343_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_268 state690 1217 state1 = (InitECandidate.Proofs.WordStages.word64_2_694,state696,1233) := by
  kernel_rfl
theorem node344_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_269 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_695,state696,1233) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_269
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node342_eq, node343_eq]
  kernel_rfl
theorem node345_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state696 1233 state1 = (InitECandidate.Proofs.WordStages.word64_2_696,state699,1237) := by
  kernel_rfl
theorem node346_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_270 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_697,state699,1237) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_270
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node344_eq, node345_eq]
  kernel_rfl
theorem node347_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state699 1237 state1 = (InitECandidate.Proofs.WordStages.word64_2_698,state701,1241) := by
  kernel_rfl
theorem node348_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_271 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_699,state701,1241) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_271
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node346_eq, node347_eq]
  kernel_rfl
theorem node349_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state701 1241 state1 = (InitECandidate.Proofs.WordStages.word64_2_702,state706,1245) := by
  kernel_rfl
theorem node350_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_272 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_703,state706,1245) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_272
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node348_eq, node349_eq]
  kernel_rfl
theorem node351_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_274 state706 1245 state1 = (InitECandidate.Proofs.WordStages.word64_2_710,state712,1261) := by
  kernel_rfl
theorem node352_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_275 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_711,state712,1261) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_275
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node350_eq, node351_eq]
  kernel_rfl
theorem node353_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state712 1261 state1 = (InitECandidate.Proofs.WordStages.word64_2_712,state715,1265) := by
  kernel_rfl
theorem node354_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_276 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_713,state715,1265) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_276
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node352_eq, node353_eq]
  kernel_rfl
theorem node355_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state715 1265 state1 = (InitECandidate.Proofs.WordStages.word64_2_714,state717,1269) := by
  kernel_rfl
theorem node356_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_277 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_715,state717,1269) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_277
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node354_eq, node355_eq]
  kernel_rfl
theorem node357_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state717 1269 state1 = (InitECandidate.Proofs.WordStages.word64_2_718,state722,1273) := by
  kernel_rfl
theorem node358_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_278 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_719,state722,1273) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_278
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node356_eq, node357_eq]
  kernel_rfl
theorem node359_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_280 state722 1273 state1 = (InitECandidate.Proofs.WordStages.word64_2_726,state728,1289) := by
  kernel_rfl
theorem node360_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_281 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_727,state728,1289) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_281
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node358_eq, node359_eq]
  kernel_rfl
theorem node361_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state728 1289 state1 = (InitECandidate.Proofs.WordStages.word64_2_728,state731,1293) := by
  kernel_rfl
theorem node362_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_282 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_729,state731,1293) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_282
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node360_eq, node361_eq]
  kernel_rfl
theorem node363_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state731 1293 state1 = (InitECandidate.Proofs.WordStages.word64_2_730,state733,1297) := by
  kernel_rfl
theorem node364_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_283 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_731,state733,1297) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_283
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node362_eq, node363_eq]
  kernel_rfl
theorem node365_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state733 1297 state1 = (InitECandidate.Proofs.WordStages.word64_2_734,state738,1301) := by
  kernel_rfl
theorem node366_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_284 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_735,state738,1301) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_284
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node364_eq, node365_eq]
  kernel_rfl
theorem node367_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_286 state738 1301 state1 = (InitECandidate.Proofs.WordStages.word64_2_742,state744,1317) := by
  kernel_rfl
theorem node368_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_287 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_743,state744,1317) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_287
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node366_eq, node367_eq]
  kernel_rfl
theorem node369_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state744 1317 state1 = (InitECandidate.Proofs.WordStages.word64_2_744,state747,1321) := by
  kernel_rfl
theorem node370_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_288 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_745,state747,1321) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_288
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node368_eq, node369_eq]
  kernel_rfl
theorem node371_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state747 1321 state1 = (InitECandidate.Proofs.WordStages.word64_2_746,state749,1325) := by
  kernel_rfl
theorem node372_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_289 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_747,state749,1325) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_289
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node370_eq, node371_eq]
  kernel_rfl
theorem node373_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state749 1325 state1 = (InitECandidate.Proofs.WordStages.word64_2_750,state754,1329) := by
  kernel_rfl
theorem node374_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_290 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_751,state754,1329) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_290
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node372_eq, node373_eq]
  kernel_rfl
theorem node375_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_292 state754 1329 state1 = (InitECandidate.Proofs.WordStages.word64_2_758,state760,1345) := by
  kernel_rfl
theorem node376_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_293 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_759,state760,1345) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_293
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node374_eq, node375_eq]
  kernel_rfl
theorem node377_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state760 1345 state1 = (InitECandidate.Proofs.WordStages.word64_2_760,state763,1349) := by
  kernel_rfl
theorem node378_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_294 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_761,state763,1349) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_294
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node376_eq, node377_eq]
  kernel_rfl
theorem node379_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state763 1349 state1 = (InitECandidate.Proofs.WordStages.word64_2_762,state765,1353) := by
  kernel_rfl
theorem node380_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_295 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_763,state765,1353) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_295
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node378_eq, node379_eq]
  kernel_rfl
theorem node381_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state765 1353 state1 = (InitECandidate.Proofs.WordStages.word64_2_766,state770,1357) := by
  kernel_rfl
theorem node382_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_296 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_767,state770,1357) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_296
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node380_eq, node381_eq]
  kernel_rfl
theorem node383_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_298 state770 1357 state1 = (InitECandidate.Proofs.WordStages.word64_2_774,state776,1373) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
