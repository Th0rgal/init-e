import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof5
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node384_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1277 state64 453 state65 = (program28488,state3447,5437) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1277
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node382_eq, node383_eq]
  kernel_rfl
theorem node385_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1284 state3447 5437 state65 = (program28549,state3493,5561) := by
  kernel_rfl
theorem node386_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1285 state64 453 state65 = (program28550,state3493,5561) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1285
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node384_eq, node385_eq]
  kernel_rfl
theorem node387_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state3493 5561 state65 = (program28559,state3517,5581) := by
  kernel_rfl
theorem node388_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1286 state64 453 state65 = (program28560,state3517,5581) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1286
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node386_eq, node387_eq]
  kernel_rfl
theorem node389_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state3517 5581 state65 = (program28561,state3528,5585) := by
  kernel_rfl
theorem node390_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1287 state64 453 state65 = (program28562,state3528,5585) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1287
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node388_eq, node389_eq]
  kernel_rfl
theorem node391_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state3528 5585 state65 = (program28622,state3569,5709) := by
  kernel_rfl
theorem node392_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1288 state64 453 state65 = (program28623,state3569,5709) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1288
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node390_eq, node391_eq]
  kernel_rfl
theorem node393_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1295 state3569 5709 state65 = (program28684,state3614,5833) := by
  kernel_rfl
theorem node394_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1296 state64 453 state65 = (program28685,state3614,5833) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1296
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node392_eq, node393_eq]
  kernel_rfl
theorem node395_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state3614 5833 state65 = (program28694,state3636,5853) := by
  kernel_rfl
theorem node396_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1297 state64 453 state65 = (program28695,state3636,5853) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1297
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node394_eq, node395_eq]
  kernel_rfl
theorem node397_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state3636 5853 state65 = (program28696,state3646,5857) := by
  kernel_rfl
theorem node398_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1298 state64 453 state65 = (program28697,state3646,5857) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1298
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node396_eq, node397_eq]
  kernel_rfl
theorem node399_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state3646 5857 state65 = (program28758,state3688,5981) := by
  kernel_rfl
theorem node400_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1299 state64 453 state65 = (program28759,state3688,5981) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1299
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node398_eq, node399_eq]
  kernel_rfl
theorem node401_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1345 state3688 5981 state65 = (program28820,state3728,6105) := by
  kernel_rfl
theorem node402_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1347 state3728 6105 state65 = (program28823,state3745,6113) := by
  kernel_rfl
theorem node403_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1348 state3688 5981 state65 = (program28824,state3745,6113) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1348
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node401_eq, node402_eq]
  kernel_rfl
theorem node404_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state3745 6113 state65 = (program28825,state3753,6117) := by
  kernel_rfl
theorem node405_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1349 state3688 5981 state65 = (program28826,state3753,6117) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1349
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node403_eq, node404_eq]
  kernel_rfl
theorem node406_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state3753 6117 state65 = (program28827,state3761,6121) := by
  kernel_rfl
theorem node407_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1350 state3688 5981 state65 = (program28828,state3761,6121) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1350
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node405_eq, node406_eq]
  kernel_rfl
theorem node408_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1351 state64 453 state65 = (program28829,state3761,6121) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1351
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node400_eq, node407_eq]
  kernel_rfl
theorem node409_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1352 state3761 6121 state65 = (program28830,state3771,6125) := by
  kernel_rfl
theorem node410_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1353 state64 453 state65 = (program28831,state3771,6125) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1353
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node408_eq, node409_eq]
  kernel_rfl
theorem node411_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1359 state3771 6125 state65 = (program28892,state3813,6249) := by
  kernel_rfl
theorem node412_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1360 state64 453 state65 = (program28893,state3813,6249) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1360
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node410_eq, node411_eq]
  kernel_rfl
theorem node413_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state3813 6249 state65 = (program28902,state3839,6269) := by
  kernel_rfl
theorem node414_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1361 state64 453 state65 = (program28903,state3839,6269) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1361
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node412_eq, node413_eq]
  kernel_rfl
theorem node415_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state3839 6269 state65 = (program28904,state3852,6273) := by
  kernel_rfl
theorem node416_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1362 state64 453 state65 = (program28905,state3852,6273) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1362
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node414_eq, node415_eq]
  kernel_rfl
theorem node417_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state3852 6273 state65 = (program28966,state3894,6397) := by
  kernel_rfl
theorem node418_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1363 state64 453 state65 = (program28967,state3894,6397) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1363
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node416_eq, node417_eq]
  kernel_rfl
theorem node419_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1399 state3894 6397 state65 = (program29028,state3930,6521) := by
  kernel_rfl
theorem node420_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1400 state3930 6521 state65 = (program29031,state3948,6529) := by
  kernel_rfl
theorem node421_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1401 state3894 6397 state65 = (program29032,state3948,6529) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1401
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node419_eq, node420_eq]
  kernel_rfl
theorem node422_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state3948 6529 state65 = (program29033,state3956,6533) := by
  kernel_rfl
theorem node423_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1402 state3894 6397 state65 = (program29034,state3956,6533) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1402
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node421_eq, node422_eq]
  kernel_rfl
theorem node424_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state3956 6533 state65 = (program29035,state3964,6537) := by
  kernel_rfl
theorem node425_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1403 state3894 6397 state65 = (program29036,state3964,6537) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1403
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node423_eq, node424_eq]
  kernel_rfl
theorem node426_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1404 state64 453 state65 = (program29037,state3964,6537) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1404
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node418_eq, node425_eq]
  kernel_rfl
theorem node427_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1405 state3964 6537 state65 = (program29038,state3975,6541) := by
  kernel_rfl
theorem node428_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1406 state64 453 state65 = (program29039,state3975,6541) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1406
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node426_eq, node427_eq]
  kernel_rfl
theorem node429_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1412 state3975 6541 state65 = (program29100,state4018,6665) := by
  kernel_rfl
theorem node430_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1413 state64 453 state65 = (program29101,state4018,6665) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1413
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node428_eq, node429_eq]
  kernel_rfl
theorem node431_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state4018 6665 state65 = (program29110,state4044,6685) := by
  kernel_rfl
theorem node432_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1414 state64 453 state65 = (program29111,state4044,6685) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1414
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node430_eq, node431_eq]
  kernel_rfl
theorem node433_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state4044 6685 state65 = (program29112,state4057,6689) := by
  kernel_rfl
theorem node434_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1415 state64 453 state65 = (program29113,state4057,6689) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1415
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node432_eq, node433_eq]
  kernel_rfl
theorem node435_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state4057 6689 state65 = (program29174,state4100,6813) := by
  kernel_rfl
theorem node436_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1416 state64 453 state65 = (program29175,state4100,6813) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1416
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node434_eq, node435_eq]
  kernel_rfl
theorem node437_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1451 state4100 6813 state65 = (program29236,state4137,6937) := by
  kernel_rfl
theorem node438_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1452 state4137 6937 state65 = (program29239,state4155,6945) := by
  kernel_rfl
theorem node439_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1453 state4100 6813 state65 = (program29240,state4155,6945) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1453
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node437_eq, node438_eq]
  kernel_rfl
theorem node440_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state4155 6945 state65 = (program29241,state4163,6949) := by
  kernel_rfl
theorem node441_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1454 state4100 6813 state65 = (program29242,state4163,6949) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1454
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node439_eq, node440_eq]
  kernel_rfl
theorem node442_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state4163 6949 state65 = (program29243,state4171,6953) := by
  kernel_rfl
theorem node443_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1455 state4100 6813 state65 = (program29244,state4171,6953) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1455
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node441_eq, node442_eq]
  kernel_rfl
theorem node444_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1456 state64 453 state65 = (program29245,state4171,6953) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1456
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node436_eq, node443_eq]
  kernel_rfl
theorem node445_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1457 state4171 6953 state65 = (program29246,state4182,6957) := by
  kernel_rfl
theorem node446_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1458 state64 453 state65 = (program29247,state4182,6957) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1458
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node444_eq, node445_eq]
  kernel_rfl
theorem node447_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1464 state4182 6957 state65 = (program29308,state4224,7081) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
