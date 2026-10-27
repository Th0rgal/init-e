import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof5
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node384_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_299 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_775,state776,1373) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_299
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node382_eq, node383_eq]
  kernel_rfl
theorem node385_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state776 1373 state1 = (InitECandidate.Proofs.WordStages.word64_2_776,state779,1377) := by
  kernel_rfl
theorem node386_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_300 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_777,state779,1377) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_300
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node384_eq, node385_eq]
  kernel_rfl
theorem node387_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state779 1377 state1 = (InitECandidate.Proofs.WordStages.word64_2_778,state781,1381) := by
  kernel_rfl
theorem node388_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_301 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_779,state781,1381) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_301
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node386_eq, node387_eq]
  kernel_rfl
theorem node389_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state781 1381 state1 = (InitECandidate.Proofs.WordStages.word64_2_782,state786,1385) := by
  kernel_rfl
theorem node390_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_302 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_783,state786,1385) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_302
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node388_eq, node389_eq]
  kernel_rfl
theorem node391_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_304 state786 1385 state1 = (InitECandidate.Proofs.WordStages.word64_2_790,state792,1401) := by
  kernel_rfl
theorem node392_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_305 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_791,state792,1401) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_305
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node390_eq, node391_eq]
  kernel_rfl
theorem node393_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state792 1401 state1 = (InitECandidate.Proofs.WordStages.word64_2_792,state795,1405) := by
  kernel_rfl
theorem node394_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_306 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_793,state795,1405) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_306
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node392_eq, node393_eq]
  kernel_rfl
theorem node395_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state795 1405 state1 = (InitECandidate.Proofs.WordStages.word64_2_794,state797,1409) := by
  kernel_rfl
theorem node396_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_307 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_795,state797,1409) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_307
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node394_eq, node395_eq]
  kernel_rfl
theorem node397_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state797 1409 state1 = (InitECandidate.Proofs.WordStages.word64_2_798,state802,1413) := by
  kernel_rfl
theorem node398_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_308 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_799,state802,1413) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_308
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node396_eq, node397_eq]
  kernel_rfl
theorem node399_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_310 state802 1413 state1 = (InitECandidate.Proofs.WordStages.word64_2_806,state808,1429) := by
  kernel_rfl
theorem node400_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_311 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_807,state808,1429) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_311
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node398_eq, node399_eq]
  kernel_rfl
theorem node401_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state808 1429 state1 = (InitECandidate.Proofs.WordStages.word64_2_808,state811,1433) := by
  kernel_rfl
theorem node402_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_312 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_809,state811,1433) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_312
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node400_eq, node401_eq]
  kernel_rfl
theorem node403_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state811 1433 state1 = (InitECandidate.Proofs.WordStages.word64_2_810,state813,1437) := by
  kernel_rfl
theorem node404_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_313 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_811,state813,1437) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_313
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node402_eq, node403_eq]
  kernel_rfl
theorem node405_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state813 1437 state1 = (InitECandidate.Proofs.WordStages.word64_2_814,state818,1441) := by
  kernel_rfl
theorem node406_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_314 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_815,state818,1441) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_314
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node404_eq, node405_eq]
  kernel_rfl
theorem node407_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_316 state818 1441 state1 = (InitECandidate.Proofs.WordStages.word64_2_822,state824,1457) := by
  kernel_rfl
theorem node408_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_317 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_823,state824,1457) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_317
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node406_eq, node407_eq]
  kernel_rfl
theorem node409_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state824 1457 state1 = (InitECandidate.Proofs.WordStages.word64_2_824,state827,1461) := by
  kernel_rfl
theorem node410_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_318 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_825,state827,1461) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_318
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node408_eq, node409_eq]
  kernel_rfl
theorem node411_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state827 1461 state1 = (InitECandidate.Proofs.WordStages.word64_2_826,state829,1465) := by
  kernel_rfl
theorem node412_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_319 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_827,state829,1465) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_319
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node410_eq, node411_eq]
  kernel_rfl
theorem node413_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state829 1465 state1 = (InitECandidate.Proofs.WordStages.word64_2_830,state834,1469) := by
  kernel_rfl
theorem node414_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_320 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_831,state834,1469) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_320
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node412_eq, node413_eq]
  kernel_rfl
theorem node415_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_322 state834 1469 state1 = (InitECandidate.Proofs.WordStages.word64_2_838,state840,1485) := by
  kernel_rfl
theorem node416_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_323 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_839,state840,1485) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_323
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node414_eq, node415_eq]
  kernel_rfl
theorem node417_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state840 1485 state1 = (InitECandidate.Proofs.WordStages.word64_2_840,state843,1489) := by
  kernel_rfl
theorem node418_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_324 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_841,state843,1489) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_324
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node416_eq, node417_eq]
  kernel_rfl
theorem node419_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state843 1489 state1 = (InitECandidate.Proofs.WordStages.word64_2_842,state845,1493) := by
  kernel_rfl
theorem node420_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_325 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_843,state845,1493) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_325
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node418_eq, node419_eq]
  kernel_rfl
theorem node421_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state845 1493 state1 = (InitECandidate.Proofs.WordStages.word64_2_846,state850,1497) := by
  kernel_rfl
theorem node422_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_326 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_847,state850,1497) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_326
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node420_eq, node421_eq]
  kernel_rfl
theorem node423_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_328 state850 1497 state1 = (InitECandidate.Proofs.WordStages.word64_2_854,state856,1513) := by
  kernel_rfl
theorem node424_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_329 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_855,state856,1513) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_329
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node422_eq, node423_eq]
  kernel_rfl
theorem node425_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state856 1513 state1 = (InitECandidate.Proofs.WordStages.word64_2_856,state859,1517) := by
  kernel_rfl
theorem node426_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_330 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_857,state859,1517) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_330
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node424_eq, node425_eq]
  kernel_rfl
theorem node427_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state859 1517 state1 = (InitECandidate.Proofs.WordStages.word64_2_858,state861,1521) := by
  kernel_rfl
theorem node428_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_331 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_859,state861,1521) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_331
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node426_eq, node427_eq]
  kernel_rfl
theorem node429_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state861 1521 state1 = (InitECandidate.Proofs.WordStages.word64_2_862,state866,1525) := by
  kernel_rfl
theorem node430_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_332 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_863,state866,1525) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_332
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node428_eq, node429_eq]
  kernel_rfl
theorem node431_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_334 state866 1525 state1 = (InitECandidate.Proofs.WordStages.word64_2_870,state872,1541) := by
  kernel_rfl
theorem node432_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_335 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_871,state872,1541) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_335
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node430_eq, node431_eq]
  kernel_rfl
theorem node433_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state872 1541 state1 = (InitECandidate.Proofs.WordStages.word64_2_872,state875,1545) := by
  kernel_rfl
theorem node434_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_336 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_873,state875,1545) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_336
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node432_eq, node433_eq]
  kernel_rfl
theorem node435_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state875 1545 state1 = (InitECandidate.Proofs.WordStages.word64_2_874,state877,1549) := by
  kernel_rfl
theorem node436_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_337 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_875,state877,1549) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_337
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node434_eq, node435_eq]
  kernel_rfl
theorem node437_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state877 1549 state1 = (InitECandidate.Proofs.WordStages.word64_2_878,state882,1553) := by
  kernel_rfl
theorem node438_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_338 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_879,state882,1553) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_338
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node436_eq, node437_eq]
  kernel_rfl
theorem node439_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_340 state882 1553 state1 = (InitECandidate.Proofs.WordStages.word64_2_886,state888,1569) := by
  kernel_rfl
theorem node440_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_341 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_887,state888,1569) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_341
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node438_eq, node439_eq]
  kernel_rfl
theorem node441_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state888 1569 state1 = (InitECandidate.Proofs.WordStages.word64_2_888,state891,1573) := by
  kernel_rfl
theorem node442_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_342 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_889,state891,1573) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_342
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node440_eq, node441_eq]
  kernel_rfl
theorem node443_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state891 1573 state1 = (InitECandidate.Proofs.WordStages.word64_2_890,state893,1577) := by
  kernel_rfl
theorem node444_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_343 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_891,state893,1577) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_343
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node442_eq, node443_eq]
  kernel_rfl
theorem node445_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state893 1577 state1 = (InitECandidate.Proofs.WordStages.word64_2_894,state898,1581) := by
  kernel_rfl
theorem node446_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_344 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_895,state898,1581) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_344
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node444_eq, node445_eq]
  kernel_rfl
theorem node447_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_346 state898 1581 state1 = (InitECandidate.Proofs.WordStages.word64_2_902,state904,1597) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
