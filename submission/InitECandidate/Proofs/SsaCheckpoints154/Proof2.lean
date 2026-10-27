import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof1
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node128_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_302 state64 453 state65 = (program26415,state910,1197) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_302
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node126_eq, node127_eq]
  kernel_rfl
theorem node129_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_316 state910 1197 state65 = (program26433,state942,1237) := by
  kernel_rfl
theorem node130_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_317 state64 453 state65 = (program26434,state942,1237) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_317
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node128_eq, node129_eq]
  kernel_rfl
theorem node131_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_319 state942 1237 state65 = (program26437,state956,1245) := by
  kernel_rfl
theorem node132_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_320 state64 453 state65 = (program26438,state956,1245) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_320
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node130_eq, node131_eq]
  kernel_rfl
theorem node133_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_163 state956 1245 state65 = (program26439,state963,1249) := by
  kernel_rfl
theorem node134_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_322 state64 453 state65 = (program26440,state963,1249) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_322
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node132_eq, node133_eq]
  kernel_rfl
theorem node135_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_324 state963 1249 state65 = (program26443,state977,1257) := by
  kernel_rfl
theorem node136_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_325 state64 453 state65 = (program26444,state977,1257) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_325
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node134_eq, node135_eq]
  kernel_rfl
theorem node137_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_167 state977 1257 state65 = (program26445,state983,1261) := by
  kernel_rfl
theorem node138_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_327 state64 453 state65 = (program26446,state983,1261) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_327
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node136_eq, node137_eq]
  kernel_rfl
theorem node139_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_329 state983 1261 state65 = (program26449,state999,1269) := by
  kernel_rfl
theorem node140_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_330 state64 453 state65 = (program26450,state999,1269) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_330
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node138_eq, node139_eq]
  kernel_rfl
theorem node141_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_171 state999 1269 state65 = (InitECandidate.Proofs.WordStages.word154_2_528,state1007,1273) := by
  kernel_rfl
theorem node142_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_332 state64 453 state65 = (program26451,state1007,1273) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_332
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node140_eq, node141_eq]
  kernel_rfl
theorem node143_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_334 state1007 1273 state65 = (program26453,state1020,1281) := by
  kernel_rfl
theorem node144_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_335 state64 453 state65 = (program26454,state1020,1281) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_335
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node142_eq, node143_eq]
  kernel_rfl
theorem node145_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_175 state1020 1281 state65 = (InitECandidate.Proofs.WordStages.word154_2_534,state1026,1285) := by
  kernel_rfl
theorem node146_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_337 state64 453 state65 = (program26455,state1026,1285) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_337
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node144_eq, node145_eq]
  kernel_rfl
theorem node147_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_351 state1026 1285 state65 = (program26473,state1058,1325) := by
  kernel_rfl
theorem node148_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_352 state64 453 state65 = (program26474,state1058,1325) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_352
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node146_eq, node147_eq]
  kernel_rfl
theorem node149_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_354 state1058 1325 state65 = (program26477,state1073,1333) := by
  kernel_rfl
theorem node150_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_355 state64 453 state65 = (program26478,state1073,1333) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_355
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node148_eq, node149_eq]
  kernel_rfl
theorem node151_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_181 state1073 1333 state65 = (program26479,state1080,1337) := by
  kernel_rfl
theorem node152_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_357 state64 453 state65 = (program26480,state1080,1337) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_357
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node150_eq, node151_eq]
  kernel_rfl
theorem node153_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_359 state1080 1337 state65 = (program26483,state1096,1345) := by
  kernel_rfl
theorem node154_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_360 state64 453 state65 = (program26484,state1096,1345) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_360
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node152_eq, node153_eq]
  kernel_rfl
theorem node155_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_185 state1096 1345 state65 = (program26485,state1104,1349) := by
  kernel_rfl
theorem node156_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_362 state64 453 state65 = (program26486,state1104,1349) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_362
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node154_eq, node155_eq]
  kernel_rfl
theorem node157_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_364 state1104 1349 state65 = (program26489,state1116,1357) := by
  kernel_rfl
theorem node158_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_365 state64 453 state65 = (program26490,state1116,1357) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_365
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node156_eq, node157_eq]
  kernel_rfl
theorem node159_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_189 state1116 1357 state65 = (InitECandidate.Proofs.WordStages.word154_2_572,state1121,1361) := by
  kernel_rfl
theorem node160_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_367 state64 453 state65 = (program26491,state1121,1361) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_367
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node158_eq, node159_eq]
  kernel_rfl
theorem node161_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_369 state1121 1361 state65 = (program26493,state1135,1369) := by
  kernel_rfl
theorem node162_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_370 state64 453 state65 = (program26494,state1135,1369) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_370
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node160_eq, node161_eq]
  kernel_rfl
theorem node163_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_193 state1135 1369 state65 = (InitECandidate.Proofs.WordStages.word154_2_578,state1142,1373) := by
  kernel_rfl
theorem node164_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_372 state64 453 state65 = (program26495,state1142,1373) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_372
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node162_eq, node163_eq]
  kernel_rfl
theorem node165_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_386 state1142 1373 state65 = (program26513,state1175,1413) := by
  kernel_rfl
theorem node166_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_387 state64 453 state65 = (program26514,state1175,1413) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_387
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node164_eq, node165_eq]
  kernel_rfl
theorem node167_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_389 state1175 1413 state65 = (program26517,state1191,1421) := by
  kernel_rfl
theorem node168_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_390 state64 453 state65 = (program26518,state1191,1421) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_390
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node166_eq, node167_eq]
  kernel_rfl
theorem node169_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_199 state1191 1421 state65 = (program26519,state1199,1425) := by
  kernel_rfl
theorem node170_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_392 state64 453 state65 = (program26520,state1199,1425) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_392
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node168_eq, node169_eq]
  kernel_rfl
theorem node171_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_394 state1199 1425 state65 = (program26523,state1212,1433) := by
  kernel_rfl
theorem node172_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_395 state64 453 state65 = (program26524,state1212,1433) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_395
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node170_eq, node171_eq]
  kernel_rfl
theorem node173_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_203 state1212 1433 state65 = (program26525,state1218,1437) := by
  kernel_rfl
theorem node174_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_397 state64 453 state65 = (program26526,state1218,1437) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_397
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node172_eq, node173_eq]
  kernel_rfl
theorem node175_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_399 state1218 1437 state65 = (program26529,state1233,1445) := by
  kernel_rfl
theorem node176_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_400 state64 453 state65 = (program26530,state1233,1445) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_400
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node174_eq, node175_eq]
  kernel_rfl
theorem node177_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_207 state1233 1445 state65 = (InitECandidate.Proofs.WordStages.word154_2_616,state1241,1449) := by
  kernel_rfl
theorem node178_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_402 state64 453 state65 = (program26531,state1241,1449) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_402
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node176_eq, node177_eq]
  kernel_rfl
theorem node179_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_404 state1241 1449 state65 = (program26533,state1256,1457) := by
  kernel_rfl
theorem node180_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_405 state64 453 state65 = (program26534,state1256,1457) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_405
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node178_eq, node179_eq]
  kernel_rfl
theorem node181_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_211 state1256 1457 state65 = (InitECandidate.Proofs.WordStages.word154_2_622,state1263,1461) := by
  kernel_rfl
theorem node182_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_407 state64 453 state65 = (program26535,state1263,1461) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_407
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node180_eq, node181_eq]
  kernel_rfl
theorem node183_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_421 state1263 1461 state65 = (program26553,state1299,1501) := by
  kernel_rfl
theorem node184_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_422 state64 453 state65 = (program26554,state1299,1501) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_422
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node182_eq, node183_eq]
  kernel_rfl
theorem node185_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_424 state1299 1501 state65 = (program26557,state1310,1509) := by
  kernel_rfl
theorem node186_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_425 state64 453 state65 = (program26558,state1310,1509) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_425
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node184_eq, node185_eq]
  kernel_rfl
theorem node187_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_217 state1310 1509 state65 = (program26559,state1314,1513) := by
  kernel_rfl
theorem node188_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_427 state64 453 state65 = (program26560,state1314,1513) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_427
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node186_eq, node187_eq]
  kernel_rfl
theorem node189_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_429 state1314 1513 state65 = (program26563,state1328,1521) := by
  kernel_rfl
theorem node190_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_430 state64 453 state65 = (program26564,state1328,1521) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_430
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node188_eq, node189_eq]
  kernel_rfl
theorem node191_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_221 state1328 1521 state65 = (program26565,state1335,1525) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
