import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof6
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node448_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1465 state64 453 state65 = (program29309,state4224,7081) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1465
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node446_eq, node447_eq]
  kernel_rfl
theorem node449_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state4224 7081 state65 = (program29318,state4247,7101) := by
  kernel_rfl
theorem node450_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1466 state64 453 state65 = (program29319,state4247,7101) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1466
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node448_eq, node449_eq]
  kernel_rfl
theorem node451_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state4247 7101 state65 = (program29320,state4259,7105) := by
  kernel_rfl
theorem node452_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1467 state64 453 state65 = (program29321,state4259,7105) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1467
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node450_eq, node451_eq]
  kernel_rfl
theorem node453_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state4259 7105 state65 = (program29382,state4301,7229) := by
  kernel_rfl
theorem node454_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1468 state64 453 state65 = (program29383,state4301,7229) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1468
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node452_eq, node453_eq]
  kernel_rfl
theorem node455_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1502 state4301 7229 state65 = (program29444,state4333,7353) := by
  kernel_rfl
theorem node456_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1503 state4333 7353 state65 = (program29447,state4350,7361) := by
  kernel_rfl
theorem node457_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1504 state4301 7229 state65 = (program29448,state4350,7361) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1504
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node455_eq, node456_eq]
  kernel_rfl
theorem node458_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state4350 7361 state65 = (program29449,state4358,7365) := by
  kernel_rfl
theorem node459_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1505 state4301 7229 state65 = (program29450,state4358,7365) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1505
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node457_eq, node458_eq]
  kernel_rfl
theorem node460_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state4358 7365 state65 = (program29451,state4366,7369) := by
  kernel_rfl
theorem node461_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1506 state4301 7229 state65 = (program29452,state4366,7369) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1506
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node459_eq, node460_eq]
  kernel_rfl
theorem node462_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1507 state64 453 state65 = (program29453,state4366,7369) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1507
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node454_eq, node461_eq]
  kernel_rfl
theorem node463_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1508 state4366 7369 state65 = (program29454,state4375,7373) := by
  kernel_rfl
theorem node464_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1509 state64 453 state65 = (program29455,state4375,7373) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1509
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node462_eq, node463_eq]
  kernel_rfl
theorem node465_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1513 state4375 7373 state65 = (program29516,state4419,7497) := by
  kernel_rfl
theorem node466_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1514 state64 453 state65 = (program29517,state4419,7497) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1514
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node464_eq, node465_eq]
  kernel_rfl
theorem node467_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state4419 7497 state65 = (program29526,state4442,7517) := by
  kernel_rfl
theorem node468_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1515 state64 453 state65 = (program29527,state4442,7517) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1515
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node466_eq, node467_eq]
  kernel_rfl
theorem node469_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state4442 7517 state65 = (program29528,state4452,7521) := by
  kernel_rfl
theorem node470_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1516 state64 453 state65 = (program29529,state4452,7521) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1516
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node468_eq, node469_eq]
  kernel_rfl
theorem node471_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state4452 7521 state65 = (program29590,state4494,7645) := by
  kernel_rfl
theorem node472_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1517 state64 453 state65 = (program29591,state4494,7645) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1517
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node470_eq, node471_eq]
  kernel_rfl
theorem node473_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1551 state4494 7645 state65 = (program29652,state4529,7769) := by
  kernel_rfl
theorem node474_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1552 state4529 7769 state65 = (program29655,state4548,7777) := by
  kernel_rfl
theorem node475_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1553 state4494 7645 state65 = (program29656,state4548,7777) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1553
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node473_eq, node474_eq]
  kernel_rfl
theorem node476_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state4548 7777 state65 = (program29657,state4556,7781) := by
  kernel_rfl
theorem node477_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1554 state4494 7645 state65 = (program29658,state4556,7781) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1554
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node475_eq, node476_eq]
  kernel_rfl
theorem node478_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state4556 7781 state65 = (program29659,state4564,7785) := by
  kernel_rfl
theorem node479_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1555 state4494 7645 state65 = (program29660,state4564,7785) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1555
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node477_eq, node478_eq]
  kernel_rfl
theorem node480_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1556 state64 453 state65 = (program29661,state4564,7785) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1556
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node472_eq, node479_eq]
  kernel_rfl
theorem node481_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1557 state4564 7785 state65 = (program29662,state4576,7789) := by
  kernel_rfl
theorem node482_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1558 state64 453 state65 = (program29663,state4576,7789) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1558
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node480_eq, node481_eq]
  kernel_rfl
theorem node483_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1561 state4576 7789 state65 = (program29724,state4618,7913) := by
  kernel_rfl
theorem node484_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1562 state64 453 state65 = (program29725,state4618,7913) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1562
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node482_eq, node483_eq]
  kernel_rfl
theorem node485_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state4618 7913 state65 = (program29734,state4644,7933) := by
  kernel_rfl
theorem node486_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1563 state64 453 state65 = (program29735,state4644,7933) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1563
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node484_eq, node485_eq]
  kernel_rfl
theorem node487_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state4644 7933 state65 = (program29736,state4657,7937) := by
  kernel_rfl
theorem node488_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1564 state64 453 state65 = (program29737,state4657,7937) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1564
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node486_eq, node487_eq]
  kernel_rfl
theorem node489_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state4657 7937 state65 = (program29798,state4697,8061) := by
  kernel_rfl
theorem node490_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1565 state64 453 state65 = (program29799,state4697,8061) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1565
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node488_eq, node489_eq]
  kernel_rfl
theorem node491_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1598 state4697 8061 state65 = (program29860,state4733,8185) := by
  kernel_rfl
theorem node492_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1599 state4733 8185 state65 = (program29863,state4751,8193) := by
  kernel_rfl
theorem node493_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1600 state4697 8061 state65 = (program29864,state4751,8193) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1600
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node491_eq, node492_eq]
  kernel_rfl
theorem node494_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state4751 8193 state65 = (program29865,state4759,8197) := by
  kernel_rfl
theorem node495_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1601 state4697 8061 state65 = (program29866,state4759,8197) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1601
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node493_eq, node494_eq]
  kernel_rfl
theorem node496_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state4759 8197 state65 = (program29867,state4767,8201) := by
  kernel_rfl
theorem node497_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1602 state4697 8061 state65 = (program29868,state4767,8201) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1602
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node495_eq, node496_eq]
  kernel_rfl
theorem node498_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1603 state64 453 state65 = (program29869,state4767,8201) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1603
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node490_eq, node497_eq]
  kernel_rfl
theorem node499_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1604 state4767 8201 state65 = (program29870,state4778,8205) := by
  kernel_rfl
theorem node500_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1605 state64 453 state65 = (program29871,state4778,8205) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1605
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node498_eq, node499_eq]
  kernel_rfl
theorem node501_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1608 state4778 8205 state65 = (program29932,state4821,8329) := by
  kernel_rfl
theorem node502_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1609 state64 453 state65 = (program29933,state4821,8329) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1609
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node500_eq, node501_eq]
  kernel_rfl
theorem node503_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state4821 8329 state65 = (program29942,state4847,8349) := by
  kernel_rfl
theorem node504_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1610 state64 453 state65 = (program29943,state4847,8349) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1610
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node502_eq, node503_eq]
  kernel_rfl
theorem node505_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state4847 8349 state65 = (program29944,state4860,8353) := by
  kernel_rfl
theorem node506_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1611 state64 453 state65 = (program29945,state4860,8353) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1611
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node504_eq, node505_eq]
  kernel_rfl
theorem node507_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state4860 8353 state65 = (program30006,state4901,8477) := by
  kernel_rfl
theorem node508_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1612 state64 453 state65 = (program30007,state4901,8477) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1612
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node506_eq, node507_eq]
  kernel_rfl
theorem node509_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1645 state4901 8477 state65 = (program30068,state4935,8601) := by
  kernel_rfl
theorem node510_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1646 state4935 8601 state65 = (program30071,state4955,8609) := by
  kernel_rfl
theorem node511_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1647 state4901 8477 state65 = (program30072,state4955,8609) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1647
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node509_eq, node510_eq]
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
