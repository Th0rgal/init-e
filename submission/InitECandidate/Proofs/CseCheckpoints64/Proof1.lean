import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints64.Proof0
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints64
theorem node64_eq : WordCse.wordCse knowledge32 InitECandidate.Proofs.WordStages.word64_2_238 = (knowledge33, InitECandidate.Proofs.WordStages.word64_2_238) := by
  rw [knowledge32_def, knowledge33_def]
  kernel_rfl
theorem node65_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_209 = (knowledge33, InitECandidate.Proofs.WordStages.word64_4_209) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node63_eq node64_eq
theorem node66_eq : WordCse.wordCse knowledge33 InitECandidate.Proofs.WordStages.word64_2_246 = (knowledge34, InitECandidate.Proofs.WordStages.word64_4_216) := by
  rw [knowledge33_def, knowledge34_def]
  kernel_rfl
theorem node67_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_217 = (knowledge34, InitECandidate.Proofs.WordStages.word64_4_217) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node65_eq node66_eq
theorem node68_eq : WordCse.wordCse knowledge34 InitECandidate.Proofs.WordStages.word64_2_250 = (knowledge35, InitECandidate.Proofs.WordStages.word64_2_250) := by
  rw [knowledge34_def, knowledge35_def]
  kernel_rfl
theorem node69_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_219 = (knowledge35, InitECandidate.Proofs.WordStages.word64_4_219) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node67_eq node68_eq
theorem node70_eq : WordCse.wordCse knowledge35 InitECandidate.Proofs.WordStages.word64_2_254 = (knowledge36, InitECandidate.Proofs.WordStages.word64_2_254) := by
  rw [knowledge35_def, knowledge36_def]
  kernel_rfl
theorem node71_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_223 = (knowledge36, InitECandidate.Proofs.WordStages.word64_4_223) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node69_eq node70_eq
theorem node72_eq : WordCse.wordCse knowledge36 InitECandidate.Proofs.WordStages.word64_2_262 = (knowledge37, InitECandidate.Proofs.WordStages.word64_4_230) := by
  rw [knowledge36_def, knowledge37_def]
  kernel_rfl
theorem node73_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_231 = (knowledge37, InitECandidate.Proofs.WordStages.word64_4_231) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node71_eq node72_eq
theorem node74_eq : WordCse.wordCse knowledge37 InitECandidate.Proofs.WordStages.word64_2_266 = (knowledge38, InitECandidate.Proofs.WordStages.word64_2_266) := by
  rw [knowledge37_def, knowledge38_def]
  kernel_rfl
theorem node75_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_233 = (knowledge38, InitECandidate.Proofs.WordStages.word64_4_233) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node73_eq node74_eq
theorem node76_eq : WordCse.wordCse knowledge38 InitECandidate.Proofs.WordStages.word64_2_270 = (knowledge39, InitECandidate.Proofs.WordStages.word64_2_270) := by
  rw [knowledge38_def, knowledge39_def]
  kernel_rfl
theorem node77_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_237 = (knowledge39, InitECandidate.Proofs.WordStages.word64_4_237) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node75_eq node76_eq
theorem node78_eq : WordCse.wordCse knowledge39 InitECandidate.Proofs.WordStages.word64_2_278 = (knowledge40, InitECandidate.Proofs.WordStages.word64_4_244) := by
  rw [knowledge39_def, knowledge40_def]
  kernel_rfl
theorem node79_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_245 = (knowledge40, InitECandidate.Proofs.WordStages.word64_4_245) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node77_eq node78_eq
theorem node80_eq : WordCse.wordCse knowledge40 InitECandidate.Proofs.WordStages.word64_2_282 = (knowledge41, InitECandidate.Proofs.WordStages.word64_2_282) := by
  rw [knowledge40_def, knowledge41_def]
  kernel_rfl
theorem node81_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_247 = (knowledge41, InitECandidate.Proofs.WordStages.word64_4_247) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node79_eq node80_eq
theorem node82_eq : WordCse.wordCse knowledge41 InitECandidate.Proofs.WordStages.word64_2_286 = (knowledge42, InitECandidate.Proofs.WordStages.word64_2_286) := by
  rw [knowledge41_def, knowledge42_def]
  kernel_rfl
theorem node83_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_251 = (knowledge42, InitECandidate.Proofs.WordStages.word64_4_251) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node81_eq node82_eq
theorem node84_eq : WordCse.wordCse knowledge42 InitECandidate.Proofs.WordStages.word64_2_294 = (knowledge43, InitECandidate.Proofs.WordStages.word64_4_258) := by
  rw [knowledge42_def, knowledge43_def]
  kernel_rfl
theorem node85_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_259 = (knowledge43, InitECandidate.Proofs.WordStages.word64_4_259) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node83_eq node84_eq
theorem node86_eq : WordCse.wordCse knowledge43 InitECandidate.Proofs.WordStages.word64_2_298 = (knowledge44, InitECandidate.Proofs.WordStages.word64_2_298) := by
  rw [knowledge43_def, knowledge44_def]
  kernel_rfl
theorem node87_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_261 = (knowledge44, InitECandidate.Proofs.WordStages.word64_4_261) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node85_eq node86_eq
theorem node88_eq : WordCse.wordCse knowledge44 InitECandidate.Proofs.WordStages.word64_2_302 = (knowledge45, InitECandidate.Proofs.WordStages.word64_2_302) := by
  rw [knowledge44_def, knowledge45_def]
  kernel_rfl
theorem node89_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_265 = (knowledge45, InitECandidate.Proofs.WordStages.word64_4_265) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node87_eq node88_eq
theorem node90_eq : WordCse.wordCse knowledge45 InitECandidate.Proofs.WordStages.word64_2_310 = (knowledge46, InitECandidate.Proofs.WordStages.word64_4_272) := by
  rw [knowledge45_def, knowledge46_def]
  kernel_rfl
theorem node91_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_273 = (knowledge46, InitECandidate.Proofs.WordStages.word64_4_273) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node89_eq node90_eq
theorem node92_eq : WordCse.wordCse knowledge46 InitECandidate.Proofs.WordStages.word64_2_314 = (knowledge47, InitECandidate.Proofs.WordStages.word64_2_314) := by
  rw [knowledge46_def, knowledge47_def]
  kernel_rfl
theorem node93_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_275 = (knowledge47, InitECandidate.Proofs.WordStages.word64_4_275) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node91_eq node92_eq
theorem node94_eq : WordCse.wordCse knowledge47 InitECandidate.Proofs.WordStages.word64_2_318 = (knowledge48, InitECandidate.Proofs.WordStages.word64_2_318) := by
  rw [knowledge47_def, knowledge48_def]
  kernel_rfl
theorem node95_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_279 = (knowledge48, InitECandidate.Proofs.WordStages.word64_4_279) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node93_eq node94_eq
theorem node96_eq : WordCse.wordCse knowledge48 InitECandidate.Proofs.WordStages.word64_2_326 = (knowledge49, InitECandidate.Proofs.WordStages.word64_4_286) := by
  rw [knowledge48_def, knowledge49_def]
  kernel_rfl
theorem node97_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_287 = (knowledge49, InitECandidate.Proofs.WordStages.word64_4_287) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node95_eq node96_eq
theorem node98_eq : WordCse.wordCse knowledge49 InitECandidate.Proofs.WordStages.word64_2_330 = (knowledge50, InitECandidate.Proofs.WordStages.word64_2_330) := by
  rw [knowledge49_def, knowledge50_def]
  kernel_rfl
theorem node99_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_289 = (knowledge50, InitECandidate.Proofs.WordStages.word64_4_289) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node97_eq node98_eq
theorem node100_eq : WordCse.wordCse knowledge50 InitECandidate.Proofs.WordStages.word64_2_334 = (knowledge51, InitECandidate.Proofs.WordStages.word64_2_334) := by
  rw [knowledge50_def, knowledge51_def]
  kernel_rfl
theorem node101_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_293 = (knowledge51, InitECandidate.Proofs.WordStages.word64_4_293) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node99_eq node100_eq
theorem node102_eq : WordCse.wordCse knowledge51 InitECandidate.Proofs.WordStages.word64_2_342 = (knowledge52, InitECandidate.Proofs.WordStages.word64_4_300) := by
  rw [knowledge51_def, knowledge52_def]
  kernel_rfl
theorem node103_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_301 = (knowledge52, InitECandidate.Proofs.WordStages.word64_4_301) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node101_eq node102_eq
theorem node104_eq : WordCse.wordCse knowledge52 InitECandidate.Proofs.WordStages.word64_2_346 = (knowledge53, InitECandidate.Proofs.WordStages.word64_2_346) := by
  rw [knowledge52_def, knowledge53_def]
  kernel_rfl
theorem node105_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_303 = (knowledge53, InitECandidate.Proofs.WordStages.word64_4_303) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node103_eq node104_eq
theorem node106_eq : WordCse.wordCse knowledge53 InitECandidate.Proofs.WordStages.word64_2_350 = (knowledge54, InitECandidate.Proofs.WordStages.word64_2_350) := by
  rw [knowledge53_def, knowledge54_def]
  kernel_rfl
theorem node107_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_307 = (knowledge54, InitECandidate.Proofs.WordStages.word64_4_307) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node105_eq node106_eq
theorem node108_eq : WordCse.wordCse knowledge54 InitECandidate.Proofs.WordStages.word64_2_358 = (knowledge55, InitECandidate.Proofs.WordStages.word64_4_314) := by
  rw [knowledge54_def, knowledge55_def]
  kernel_rfl
theorem node109_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_315 = (knowledge55, InitECandidate.Proofs.WordStages.word64_4_315) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node107_eq node108_eq
theorem node110_eq : WordCse.wordCse knowledge55 InitECandidate.Proofs.WordStages.word64_2_362 = (knowledge56, InitECandidate.Proofs.WordStages.word64_2_362) := by
  rw [knowledge55_def, knowledge56_def]
  kernel_rfl
theorem node111_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_317 = (knowledge56, InitECandidate.Proofs.WordStages.word64_4_317) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node109_eq node110_eq
theorem node112_eq : WordCse.wordCse knowledge56 InitECandidate.Proofs.WordStages.word64_2_366 = (knowledge57, InitECandidate.Proofs.WordStages.word64_2_366) := by
  rw [knowledge56_def, knowledge57_def]
  kernel_rfl
theorem node113_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_321 = (knowledge57, InitECandidate.Proofs.WordStages.word64_4_321) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node111_eq node112_eq
theorem node114_eq : WordCse.wordCse knowledge57 InitECandidate.Proofs.WordStages.word64_2_374 = (knowledge58, InitECandidate.Proofs.WordStages.word64_4_328) := by
  rw [knowledge57_def, knowledge58_def]
  kernel_rfl
theorem node115_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_329 = (knowledge58, InitECandidate.Proofs.WordStages.word64_4_329) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node113_eq node114_eq
theorem node116_eq : WordCse.wordCse knowledge58 InitECandidate.Proofs.WordStages.word64_2_378 = (knowledge59, InitECandidate.Proofs.WordStages.word64_2_378) := by
  rw [knowledge58_def, knowledge59_def]
  kernel_rfl
theorem node117_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_331 = (knowledge59, InitECandidate.Proofs.WordStages.word64_4_331) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node115_eq node116_eq
theorem node118_eq : WordCse.wordCse knowledge59 InitECandidate.Proofs.WordStages.word64_2_382 = (knowledge60, InitECandidate.Proofs.WordStages.word64_2_382) := by
  rw [knowledge59_def, knowledge60_def]
  kernel_rfl
theorem node119_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_335 = (knowledge60, InitECandidate.Proofs.WordStages.word64_4_335) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node117_eq node118_eq
theorem node120_eq : WordCse.wordCse knowledge60 InitECandidate.Proofs.WordStages.word64_2_390 = (knowledge61, InitECandidate.Proofs.WordStages.word64_4_342) := by
  rw [knowledge60_def, knowledge61_def]
  kernel_rfl
theorem node121_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_343 = (knowledge61, InitECandidate.Proofs.WordStages.word64_4_343) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node119_eq node120_eq
theorem node122_eq : WordCse.wordCse knowledge61 InitECandidate.Proofs.WordStages.word64_2_394 = (knowledge62, InitECandidate.Proofs.WordStages.word64_2_394) := by
  rw [knowledge61_def, knowledge62_def]
  kernel_rfl
theorem node123_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_345 = (knowledge62, InitECandidate.Proofs.WordStages.word64_4_345) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node121_eq node122_eq
theorem node124_eq : WordCse.wordCse knowledge62 InitECandidate.Proofs.WordStages.word64_2_398 = (knowledge63, InitECandidate.Proofs.WordStages.word64_2_398) := by
  rw [knowledge62_def, knowledge63_def]
  kernel_rfl
theorem node125_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_349 = (knowledge63, InitECandidate.Proofs.WordStages.word64_4_349) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node123_eq node124_eq
theorem node126_eq : WordCse.wordCse knowledge63 InitECandidate.Proofs.WordStages.word64_2_406 = (knowledge64, InitECandidate.Proofs.WordStages.word64_4_356) := by
  rw [knowledge63_def, knowledge64_def]
  kernel_rfl
theorem node127_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_357 = (knowledge64, InitECandidate.Proofs.WordStages.word64_4_357) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node125_eq node126_eq
end InitECandidate.Proofs.CseCheckpoints64
