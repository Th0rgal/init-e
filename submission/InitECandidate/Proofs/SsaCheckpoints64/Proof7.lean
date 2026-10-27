import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints64.Proof6
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints64
theorem node448_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_347 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_903,state904,1597) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_347
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node446_eq, node447_eq]
  kernel_rfl
theorem node449_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state904 1597 state1 = (InitECandidate.Proofs.WordStages.word64_2_904,state907,1601) := by
  kernel_rfl
theorem node450_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_348 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_905,state907,1601) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_348
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node448_eq, node449_eq]
  kernel_rfl
theorem node451_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state907 1601 state1 = (InitECandidate.Proofs.WordStages.word64_2_906,state909,1605) := by
  kernel_rfl
theorem node452_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_349 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_907,state909,1605) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_349
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node450_eq, node451_eq]
  kernel_rfl
theorem node453_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state909 1605 state1 = (InitECandidate.Proofs.WordStages.word64_2_910,state914,1609) := by
  kernel_rfl
theorem node454_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_350 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_911,state914,1609) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_350
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node452_eq, node453_eq]
  kernel_rfl
theorem node455_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_352 state914 1609 state1 = (InitECandidate.Proofs.WordStages.word64_2_918,state920,1625) := by
  kernel_rfl
theorem node456_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_353 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_919,state920,1625) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_353
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node454_eq, node455_eq]
  kernel_rfl
theorem node457_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state920 1625 state1 = (InitECandidate.Proofs.WordStages.word64_2_920,state923,1629) := by
  kernel_rfl
theorem node458_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_354 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_921,state923,1629) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_354
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node456_eq, node457_eq]
  kernel_rfl
theorem node459_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state923 1629 state1 = (InitECandidate.Proofs.WordStages.word64_2_922,state925,1633) := by
  kernel_rfl
theorem node460_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_355 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_923,state925,1633) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_355
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node458_eq, node459_eq]
  kernel_rfl
theorem node461_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state925 1633 state1 = (InitECandidate.Proofs.WordStages.word64_2_926,state930,1637) := by
  kernel_rfl
theorem node462_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_356 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_927,state930,1637) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_356
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node460_eq, node461_eq]
  kernel_rfl
theorem node463_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_358 state930 1637 state1 = (InitECandidate.Proofs.WordStages.word64_2_934,state936,1653) := by
  kernel_rfl
theorem node464_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_359 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_935,state936,1653) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_359
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node462_eq, node463_eq]
  kernel_rfl
theorem node465_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state936 1653 state1 = (InitECandidate.Proofs.WordStages.word64_2_936,state939,1657) := by
  kernel_rfl
theorem node466_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_360 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_937,state939,1657) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_360
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node464_eq, node465_eq]
  kernel_rfl
theorem node467_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state939 1657 state1 = (InitECandidate.Proofs.WordStages.word64_2_938,state941,1661) := by
  kernel_rfl
theorem node468_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_361 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_939,state941,1661) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_361
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node466_eq, node467_eq]
  kernel_rfl
theorem node469_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state941 1661 state1 = (InitECandidate.Proofs.WordStages.word64_2_942,state946,1665) := by
  kernel_rfl
theorem node470_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_362 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_943,state946,1665) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_362
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node468_eq, node469_eq]
  kernel_rfl
theorem node471_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_364 state946 1665 state1 = (InitECandidate.Proofs.WordStages.word64_2_950,state952,1681) := by
  kernel_rfl
theorem node472_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_365 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_951,state952,1681) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_365
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node470_eq, node471_eq]
  kernel_rfl
theorem node473_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state952 1681 state1 = (InitECandidate.Proofs.WordStages.word64_2_952,state955,1685) := by
  kernel_rfl
theorem node474_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_366 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_953,state955,1685) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_366
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node472_eq, node473_eq]
  kernel_rfl
theorem node475_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state955 1685 state1 = (InitECandidate.Proofs.WordStages.word64_2_954,state957,1689) := by
  kernel_rfl
theorem node476_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_367 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_955,state957,1689) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_367
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node474_eq, node475_eq]
  kernel_rfl
theorem node477_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state957 1689 state1 = (InitECandidate.Proofs.WordStages.word64_2_958,state962,1693) := by
  kernel_rfl
theorem node478_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_368 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_959,state962,1693) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_368
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node476_eq, node477_eq]
  kernel_rfl
theorem node479_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_370 state962 1693 state1 = (InitECandidate.Proofs.WordStages.word64_2_966,state968,1709) := by
  kernel_rfl
theorem node480_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_371 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_967,state968,1709) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_371
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node478_eq, node479_eq]
  kernel_rfl
theorem node481_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state968 1709 state1 = (InitECandidate.Proofs.WordStages.word64_2_968,state971,1713) := by
  kernel_rfl
theorem node482_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_372 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_969,state971,1713) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_372
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node480_eq, node481_eq]
  kernel_rfl
theorem node483_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state971 1713 state1 = (InitECandidate.Proofs.WordStages.word64_2_970,state973,1717) := by
  kernel_rfl
theorem node484_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_373 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_971,state973,1717) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_373
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node482_eq, node483_eq]
  kernel_rfl
theorem node485_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state973 1717 state1 = (InitECandidate.Proofs.WordStages.word64_2_974,state978,1721) := by
  kernel_rfl
theorem node486_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_374 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_975,state978,1721) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_374
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node484_eq, node485_eq]
  kernel_rfl
theorem node487_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_376 state978 1721 state1 = (InitECandidate.Proofs.WordStages.word64_2_982,state984,1737) := by
  kernel_rfl
theorem node488_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_377 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_983,state984,1737) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_377
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node486_eq, node487_eq]
  kernel_rfl
theorem node489_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state984 1737 state1 = (InitECandidate.Proofs.WordStages.word64_2_984,state987,1741) := by
  kernel_rfl
theorem node490_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_378 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_985,state987,1741) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_378
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node488_eq, node489_eq]
  kernel_rfl
theorem node491_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state987 1741 state1 = (InitECandidate.Proofs.WordStages.word64_2_986,state989,1745) := by
  kernel_rfl
theorem node492_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_379 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_987,state989,1745) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_379
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node490_eq, node491_eq]
  kernel_rfl
theorem node493_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state989 1745 state1 = (InitECandidate.Proofs.WordStages.word64_2_990,state994,1749) := by
  kernel_rfl
theorem node494_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_380 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_991,state994,1749) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_380
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node492_eq, node493_eq]
  kernel_rfl
theorem node495_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_382 state994 1749 state1 = (InitECandidate.Proofs.WordStages.word64_2_998,state1000,1765) := by
  kernel_rfl
theorem node496_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_383 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_999,state1000,1765) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_383
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node494_eq, node495_eq]
  kernel_rfl
theorem node497_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state1000 1765 state1 = (InitECandidate.Proofs.WordStages.word64_2_1000,state1003,1769) := by
  kernel_rfl
theorem node498_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_384 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1001,state1003,1769) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_384
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node496_eq, node497_eq]
  kernel_rfl
theorem node499_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state1003 1769 state1 = (InitECandidate.Proofs.WordStages.word64_2_1002,state1005,1773) := by
  kernel_rfl
theorem node500_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_385 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1003,state1005,1773) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_385
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node498_eq, node499_eq]
  kernel_rfl
theorem node501_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state1005 1773 state1 = (InitECandidate.Proofs.WordStages.word64_2_1006,state1010,1777) := by
  kernel_rfl
theorem node502_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_386 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1007,state1010,1777) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_386
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node500_eq, node501_eq]
  kernel_rfl
theorem node503_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_388 state1010 1777 state1 = (InitECandidate.Proofs.WordStages.word64_2_1014,state1016,1793) := by
  kernel_rfl
theorem node504_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_389 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1015,state1016,1793) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_389
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node502_eq, node503_eq]
  kernel_rfl
theorem node505_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_7 state1016 1793 state1 = (InitECandidate.Proofs.WordStages.word64_2_1016,state1019,1797) := by
  kernel_rfl
theorem node506_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_390 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1017,state1019,1797) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_390
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node504_eq, node505_eq]
  kernel_rfl
theorem node507_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_9 state1019 1797 state1 = (InitECandidate.Proofs.WordStages.word64_2_1018,state1021,1801) := by
  kernel_rfl
theorem node508_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_391 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1019,state1021,1801) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_391
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node506_eq, node507_eq]
  kernel_rfl
theorem node509_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_13 state1021 1801 state1 = (InitECandidate.Proofs.WordStages.word64_2_1022,state1026,1805) := by
  kernel_rfl
theorem node510_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_392 state0 13 state1 = (InitECandidate.Proofs.WordStages.word64_2_1023,state1026,1805) := by
  unfold InitECandidate.Proofs.WordStages.word64_1_392
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node508_eq, node509_eq]
  kernel_rfl
theorem node511_eq : ssaStructural InitECandidate.Proofs.WordStages.word64_1_394 state1026 1805 state1 = (InitECandidate.Proofs.WordStages.word64_2_1030,state1032,1821) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints64
