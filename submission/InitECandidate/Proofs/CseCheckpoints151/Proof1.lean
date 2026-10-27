import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof0
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node64_eq : WordCse.wordCse knowledge32 InitECandidate.Proofs.WordStages.word151_2_226 = (knowledge33, InitECandidate.Proofs.WordStages.word151_2_226) := by
  rw [knowledge32_def, knowledge33_def]
  kernel_rfl
theorem node65_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_227 = (knowledge33, InitECandidate.Proofs.WordStages.word151_2_227) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node63_eq node64_eq
theorem node66_eq : WordCse.wordCse knowledge33 InitECandidate.Proofs.WordStages.word151_2_228 = (knowledge34, InitECandidate.Proofs.WordStages.word151_2_228) := by
  rw [knowledge33_def, knowledge34_def]
  kernel_rfl
theorem node67_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_229 = (knowledge34, InitECandidate.Proofs.WordStages.word151_2_229) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node65_eq node66_eq
theorem node68_eq : WordCse.wordCse knowledge34 InitECandidate.Proofs.WordStages.word151_2_232 = (knowledge35, InitECandidate.Proofs.WordStages.word151_2_232) := by
  rw [knowledge34_def, knowledge35_def]
  kernel_rfl
theorem node69_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_233 = (knowledge35, InitECandidate.Proofs.WordStages.word151_2_233) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node67_eq node68_eq
theorem node70_eq : WordCse.wordCse knowledge35 InitECandidate.Proofs.WordStages.word151_2_234 = (knowledge36, InitECandidate.Proofs.WordStages.word151_2_234) := by
  rw [knowledge35_def, knowledge36_def]
  kernel_rfl
theorem node71_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_235 = (knowledge36, InitECandidate.Proofs.WordStages.word151_2_235) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node69_eq node70_eq
theorem node72_eq : WordCse.wordCse knowledge36 InitECandidate.Proofs.WordStages.word151_2_238 = (knowledge37, InitECandidate.Proofs.WordStages.word151_2_238) := by
  rw [knowledge36_def, knowledge37_def]
  kernel_rfl
theorem node73_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_239 = (knowledge37, InitECandidate.Proofs.WordStages.word151_2_239) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node71_eq node72_eq
theorem node74_eq : WordCse.wordCse knowledge37 InitECandidate.Proofs.WordStages.word151_2_240 = (knowledge38, InitECandidate.Proofs.WordStages.word151_2_240) := by
  rw [knowledge37_def, knowledge38_def]
  kernel_rfl
theorem node75_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_241 = (knowledge38, InitECandidate.Proofs.WordStages.word151_2_241) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node73_eq node74_eq
theorem node76_eq : WordCse.wordCse knowledge38 InitECandidate.Proofs.WordStages.word151_2_260 = (knowledge39, InitECandidate.Proofs.WordStages.word151_2_260) := by
  rw [knowledge38_def, knowledge39_def]
  kernel_rfl
theorem node77_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_261 = (knowledge39, InitECandidate.Proofs.WordStages.word151_2_261) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node75_eq node76_eq
theorem node78_eq : WordCse.wordCse knowledge39 InitECandidate.Proofs.WordStages.word151_2_264 = (knowledge40, InitECandidate.Proofs.WordStages.word151_2_264) := by
  rw [knowledge39_def, knowledge40_def]
  kernel_rfl
theorem node79_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_265 = (knowledge40, InitECandidate.Proofs.WordStages.word151_2_265) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node77_eq node78_eq
theorem node80_eq : WordCse.wordCse knowledge40 InitECandidate.Proofs.WordStages.word151_2_266 = (knowledge41, InitECandidate.Proofs.WordStages.word151_2_266) := by
  rw [knowledge40_def, knowledge41_def]
  kernel_rfl
theorem node81_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_267 = (knowledge41, InitECandidate.Proofs.WordStages.word151_2_267) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node79_eq node80_eq
theorem node82_eq : WordCse.wordCse knowledge41 InitECandidate.Proofs.WordStages.word151_2_270 = (knowledge42, InitECandidate.Proofs.WordStages.word151_2_270) := by
  rw [knowledge41_def, knowledge42_def]
  kernel_rfl
theorem node83_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_271 = (knowledge42, InitECandidate.Proofs.WordStages.word151_2_271) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node81_eq node82_eq
theorem node84_eq : WordCse.wordCse knowledge42 InitECandidate.Proofs.WordStages.word151_2_272 = (knowledge43, InitECandidate.Proofs.WordStages.word151_2_272) := by
  rw [knowledge42_def, knowledge43_def]
  kernel_rfl
theorem node85_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_273 = (knowledge43, InitECandidate.Proofs.WordStages.word151_2_273) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node83_eq node84_eq
theorem node86_eq : WordCse.wordCse knowledge43 InitECandidate.Proofs.WordStages.word151_2_276 = (knowledge44, InitECandidate.Proofs.WordStages.word151_2_276) := by
  rw [knowledge43_def, knowledge44_def]
  kernel_rfl
theorem node87_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_277 = (knowledge44, InitECandidate.Proofs.WordStages.word151_2_277) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node85_eq node86_eq
theorem node88_eq : WordCse.wordCse knowledge44 InitECandidate.Proofs.WordStages.word151_2_278 = (knowledge45, InitECandidate.Proofs.WordStages.word151_2_278) := by
  rw [knowledge44_def, knowledge45_def]
  kernel_rfl
theorem node89_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_279 = (knowledge45, InitECandidate.Proofs.WordStages.word151_2_279) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node87_eq node88_eq
theorem node90_eq : WordCse.wordCse knowledge45 InitECandidate.Proofs.WordStages.word151_2_282 = (knowledge46, InitECandidate.Proofs.WordStages.word151_2_282) := by
  rw [knowledge45_def, knowledge46_def]
  kernel_rfl
theorem node91_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_283 = (knowledge46, InitECandidate.Proofs.WordStages.word151_2_283) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node89_eq node90_eq
theorem node92_eq : WordCse.wordCse knowledge46 InitECandidate.Proofs.WordStages.word151_2_284 = (knowledge47, InitECandidate.Proofs.WordStages.word151_2_284) := by
  rw [knowledge46_def, knowledge47_def]
  kernel_rfl
theorem node93_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_285 = (knowledge47, InitECandidate.Proofs.WordStages.word151_2_285) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node91_eq node92_eq
theorem node94_eq : WordCse.wordCse knowledge47 InitECandidate.Proofs.WordStages.word151_2_304 = (knowledge48, InitECandidate.Proofs.WordStages.word151_2_304) := by
  rw [knowledge47_def, knowledge48_def]
  kernel_rfl
theorem node95_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_305 = (knowledge48, InitECandidate.Proofs.WordStages.word151_2_305) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node93_eq node94_eq
theorem node96_eq : WordCse.wordCse knowledge48 InitECandidate.Proofs.WordStages.word151_2_308 = (knowledge49, InitECandidate.Proofs.WordStages.word151_2_308) := by
  rw [knowledge48_def, knowledge49_def]
  kernel_rfl
theorem node97_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_309 = (knowledge49, InitECandidate.Proofs.WordStages.word151_2_309) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node95_eq node96_eq
theorem node98_eq : WordCse.wordCse knowledge49 InitECandidate.Proofs.WordStages.word151_2_310 = (knowledge50, InitECandidate.Proofs.WordStages.word151_2_310) := by
  rw [knowledge49_def, knowledge50_def]
  kernel_rfl
theorem node99_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_311 = (knowledge50, InitECandidate.Proofs.WordStages.word151_2_311) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node97_eq node98_eq
theorem node100_eq : WordCse.wordCse knowledge50 InitECandidate.Proofs.WordStages.word151_2_314 = (knowledge51, InitECandidate.Proofs.WordStages.word151_2_314) := by
  rw [knowledge50_def, knowledge51_def]
  kernel_rfl
theorem node101_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_315 = (knowledge51, InitECandidate.Proofs.WordStages.word151_2_315) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node99_eq node100_eq
theorem node102_eq : WordCse.wordCse knowledge51 InitECandidate.Proofs.WordStages.word151_2_316 = (knowledge52, InitECandidate.Proofs.WordStages.word151_2_316) := by
  rw [knowledge51_def, knowledge52_def]
  kernel_rfl
theorem node103_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_317 = (knowledge52, InitECandidate.Proofs.WordStages.word151_2_317) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node101_eq node102_eq
theorem node104_eq : WordCse.wordCse knowledge52 InitECandidate.Proofs.WordStages.word151_2_320 = (knowledge53, InitECandidate.Proofs.WordStages.word151_2_320) := by
  rw [knowledge52_def, knowledge53_def]
  kernel_rfl
theorem node105_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_321 = (knowledge53, InitECandidate.Proofs.WordStages.word151_2_321) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node103_eq node104_eq
theorem node106_eq : WordCse.wordCse knowledge53 InitECandidate.Proofs.WordStages.word151_2_322 = (knowledge54, InitECandidate.Proofs.WordStages.word151_2_322) := by
  rw [knowledge53_def, knowledge54_def]
  kernel_rfl
theorem node107_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_323 = (knowledge54, InitECandidate.Proofs.WordStages.word151_2_323) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node105_eq node106_eq
theorem node108_eq : WordCse.wordCse knowledge54 InitECandidate.Proofs.WordStages.word151_2_326 = (knowledge55, InitECandidate.Proofs.WordStages.word151_2_326) := by
  rw [knowledge54_def, knowledge55_def]
  kernel_rfl
theorem node109_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_327 = (knowledge55, InitECandidate.Proofs.WordStages.word151_2_327) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node107_eq node108_eq
theorem node110_eq : WordCse.wordCse knowledge55 InitECandidate.Proofs.WordStages.word151_2_328 = (knowledge56, InitECandidate.Proofs.WordStages.word151_2_328) := by
  rw [knowledge55_def, knowledge56_def]
  kernel_rfl
theorem node111_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_329 = (knowledge56, InitECandidate.Proofs.WordStages.word151_2_329) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node109_eq node110_eq
theorem node112_eq : WordCse.wordCse knowledge56 InitECandidate.Proofs.WordStages.word151_2_348 = (knowledge57, InitECandidate.Proofs.WordStages.word151_2_348) := by
  rw [knowledge56_def, knowledge57_def]
  kernel_rfl
theorem node113_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_349 = (knowledge57, InitECandidate.Proofs.WordStages.word151_2_349) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node111_eq node112_eq
theorem node114_eq : WordCse.wordCse knowledge57 InitECandidate.Proofs.WordStages.word151_2_352 = (knowledge58, InitECandidate.Proofs.WordStages.word151_2_352) := by
  rw [knowledge57_def, knowledge58_def]
  kernel_rfl
theorem node115_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_353 = (knowledge58, InitECandidate.Proofs.WordStages.word151_2_353) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node113_eq node114_eq
theorem node116_eq : WordCse.wordCse knowledge58 InitECandidate.Proofs.WordStages.word151_2_354 = (knowledge59, InitECandidate.Proofs.WordStages.word151_2_354) := by
  rw [knowledge58_def, knowledge59_def]
  kernel_rfl
theorem node117_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_355 = (knowledge59, InitECandidate.Proofs.WordStages.word151_2_355) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node115_eq node116_eq
theorem node118_eq : WordCse.wordCse knowledge59 InitECandidate.Proofs.WordStages.word151_2_358 = (knowledge60, InitECandidate.Proofs.WordStages.word151_2_358) := by
  rw [knowledge59_def, knowledge60_def]
  kernel_rfl
theorem node119_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_359 = (knowledge60, InitECandidate.Proofs.WordStages.word151_2_359) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node117_eq node118_eq
theorem node120_eq : WordCse.wordCse knowledge60 InitECandidate.Proofs.WordStages.word151_2_360 = (knowledge61, InitECandidate.Proofs.WordStages.word151_2_360) := by
  rw [knowledge60_def, knowledge61_def]
  kernel_rfl
theorem node121_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_361 = (knowledge61, InitECandidate.Proofs.WordStages.word151_2_361) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node119_eq node120_eq
theorem node122_eq : WordCse.wordCse knowledge61 InitECandidate.Proofs.WordStages.word151_2_364 = (knowledge62, InitECandidate.Proofs.WordStages.word151_2_364) := by
  rw [knowledge61_def, knowledge62_def]
  kernel_rfl
theorem node123_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_365 = (knowledge62, InitECandidate.Proofs.WordStages.word151_2_365) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node121_eq node122_eq
theorem node124_eq : WordCse.wordCse knowledge62 InitECandidate.Proofs.WordStages.word151_2_366 = (knowledge63, InitECandidate.Proofs.WordStages.word151_2_366) := by
  rw [knowledge62_def, knowledge63_def]
  kernel_rfl
theorem node125_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_367 = (knowledge63, InitECandidate.Proofs.WordStages.word151_2_367) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node123_eq node124_eq
theorem node126_eq : WordCse.wordCse knowledge63 InitECandidate.Proofs.WordStages.word151_2_370 = (knowledge64, InitECandidate.Proofs.WordStages.word151_2_370) := by
  rw [knowledge63_def, knowledge64_def]
  kernel_rfl
theorem node127_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_371 = (knowledge64, InitECandidate.Proofs.WordStages.word151_2_371) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node125_eq node126_eq
end InitECandidate.Proofs.CseCheckpoints151
