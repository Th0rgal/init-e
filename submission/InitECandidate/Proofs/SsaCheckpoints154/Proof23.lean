import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof22
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1472_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2579 state64 453 state65 = (program41585,state16344,31949) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2579
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1470_eq, node1471_eq]
  kernel_rfl
theorem node1473_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2582 state16344 31949 state65 = (program41639,state16387,32065) := by
  kernel_rfl
theorem node1474_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2583 state64 453 state65 = (program41640,state16387,32065) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2583
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1472_eq, node1473_eq]
  kernel_rfl
theorem node1475_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state16387 32065 state65 = (program41649,state16411,32085) := by
  kernel_rfl
theorem node1476_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2584 state64 453 state65 = (program41650,state16411,32085) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2584
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1474_eq, node1475_eq]
  kernel_rfl
theorem node1477_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state16411 32085 state65 = (program41651,state16422,32089) := by
  kernel_rfl
theorem node1478_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2585 state64 453 state65 = (program41652,state16422,32089) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2585
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1476_eq, node1477_eq]
  kernel_rfl
theorem node1479_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state16422 32089 state65 = (program41709,state16463,32213) := by
  kernel_rfl
theorem node1480_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2586 state64 453 state65 = (program41710,state16463,32213) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2586
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1478_eq, node1479_eq]
  kernel_rfl
theorem node1481_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2589 state16463 32213 state65 = (program41764,state16505,32329) := by
  kernel_rfl
theorem node1482_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2590 state64 453 state65 = (program41765,state16505,32329) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2590
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1480_eq, node1481_eq]
  kernel_rfl
theorem node1483_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state16505 32329 state65 = (program41774,state16527,32349) := by
  kernel_rfl
theorem node1484_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2591 state64 453 state65 = (program41775,state16527,32349) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2591
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1482_eq, node1483_eq]
  kernel_rfl
theorem node1485_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state16527 32349 state65 = (program41776,state16537,32353) := by
  kernel_rfl
theorem node1486_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2592 state64 453 state65 = (program41777,state16537,32353) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2592
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1484_eq, node1485_eq]
  kernel_rfl
theorem node1487_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state16537 32353 state65 = (program41834,state16579,32477) := by
  kernel_rfl
theorem node1488_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2593 state64 453 state65 = (program41835,state16579,32477) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2593
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1486_eq, node1487_eq]
  kernel_rfl
theorem node1489_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2596 state16579 32477 state65 = (program41889,state16621,32593) := by
  kernel_rfl
theorem node1490_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2597 state64 453 state65 = (program41890,state16621,32593) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2597
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1488_eq, node1489_eq]
  kernel_rfl
theorem node1491_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state16621 32593 state65 = (program41899,state16647,32613) := by
  kernel_rfl
theorem node1492_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2598 state64 453 state65 = (program41900,state16647,32613) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2598
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1490_eq, node1491_eq]
  kernel_rfl
theorem node1493_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state16647 32613 state65 = (program41901,state16660,32617) := by
  kernel_rfl
theorem node1494_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2599 state64 453 state65 = (program41902,state16660,32617) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2599
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1492_eq, node1493_eq]
  kernel_rfl
theorem node1495_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state16660 32617 state65 = (program41959,state16702,32741) := by
  kernel_rfl
theorem node1496_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2600 state64 453 state65 = (program41960,state16702,32741) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2600
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1494_eq, node1495_eq]
  kernel_rfl
theorem node1497_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2603 state16702 32741 state65 = (program42014,state16742,32857) := by
  kernel_rfl
theorem node1498_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2604 state64 453 state65 = (program42015,state16742,32857) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2604
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1496_eq, node1497_eq]
  kernel_rfl
theorem node1499_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state16742 32857 state65 = (program42024,state16768,32877) := by
  kernel_rfl
theorem node1500_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2605 state64 453 state65 = (program42025,state16768,32877) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2605
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1498_eq, node1499_eq]
  kernel_rfl
theorem node1501_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state16768 32877 state65 = (program42026,state16781,32881) := by
  kernel_rfl
theorem node1502_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2606 state64 453 state65 = (program42027,state16781,32881) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2606
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1500_eq, node1501_eq]
  kernel_rfl
theorem node1503_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state16781 32881 state65 = (program42084,state16824,33005) := by
  kernel_rfl
theorem node1504_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2607 state64 453 state65 = (program42085,state16824,33005) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2607
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1502_eq, node1503_eq]
  kernel_rfl
theorem node1505_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2610 state16824 33005 state65 = (program42139,state16865,33121) := by
  kernel_rfl
theorem node1506_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2611 state64 453 state65 = (program42140,state16865,33121) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2611
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1504_eq, node1505_eq]
  kernel_rfl
theorem node1507_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state16865 33121 state65 = (program42149,state16888,33141) := by
  kernel_rfl
theorem node1508_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2612 state64 453 state65 = (program42150,state16888,33141) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2612
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1506_eq, node1507_eq]
  kernel_rfl
theorem node1509_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state16888 33141 state65 = (program42151,state16900,33145) := by
  kernel_rfl
theorem node1510_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2613 state64 453 state65 = (program42152,state16900,33145) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2613
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1508_eq, node1509_eq]
  kernel_rfl
theorem node1511_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state16900 33145 state65 = (program42209,state16942,33269) := by
  kernel_rfl
theorem node1512_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2614 state64 453 state65 = (program42210,state16942,33269) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2614
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1510_eq, node1511_eq]
  kernel_rfl
theorem node1513_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2617 state16942 33269 state65 = (program42264,state16983,33385) := by
  kernel_rfl
theorem node1514_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2618 state64 453 state65 = (program42265,state16983,33385) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2618
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1512_eq, node1513_eq]
  kernel_rfl
theorem node1515_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state16983 33385 state65 = (program42274,state17006,33405) := by
  kernel_rfl
theorem node1516_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2619 state64 453 state65 = (program42275,state17006,33405) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2619
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1514_eq, node1515_eq]
  kernel_rfl
theorem node1517_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state17006 33405 state65 = (program42276,state17016,33409) := by
  kernel_rfl
theorem node1518_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2620 state64 453 state65 = (program42277,state17016,33409) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2620
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1516_eq, node1517_eq]
  kernel_rfl
theorem node1519_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state17016 33409 state65 = (program42334,state17058,33533) := by
  kernel_rfl
theorem node1520_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2621 state64 453 state65 = (program42335,state17058,33533) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2621
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1518_eq, node1519_eq]
  kernel_rfl
theorem node1521_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2624 state17058 33533 state65 = (program42389,state17100,33649) := by
  kernel_rfl
theorem node1522_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2625 state64 453 state65 = (program42390,state17100,33649) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2625
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1520_eq, node1521_eq]
  kernel_rfl
theorem node1523_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state17100 33649 state65 = (program42399,state17126,33669) := by
  kernel_rfl
theorem node1524_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2626 state64 453 state65 = (program42400,state17126,33669) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2626
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1522_eq, node1523_eq]
  kernel_rfl
theorem node1525_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state17126 33669 state65 = (program42401,state17139,33673) := by
  kernel_rfl
theorem node1526_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2627 state64 453 state65 = (program42402,state17139,33673) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2627
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1524_eq, node1525_eq]
  kernel_rfl
theorem node1527_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state17139 33673 state65 = (program42459,state17179,33797) := by
  kernel_rfl
theorem node1528_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2628 state64 453 state65 = (program42460,state17179,33797) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2628
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1526_eq, node1527_eq]
  kernel_rfl
theorem node1529_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2631 state17179 33797 state65 = (program42514,state17221,33913) := by
  kernel_rfl
theorem node1530_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2632 state64 453 state65 = (program42515,state17221,33913) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2632
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1528_eq, node1529_eq]
  kernel_rfl
theorem node1531_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state17221 33913 state65 = (program42524,state17247,33933) := by
  kernel_rfl
theorem node1532_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2633 state64 453 state65 = (program42525,state17247,33933) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2633
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1530_eq, node1531_eq]
  kernel_rfl
theorem node1533_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state17247 33933 state65 = (program42526,state17260,33937) := by
  kernel_rfl
theorem node1534_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2634 state64 453 state65 = (program42527,state17260,33937) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2634
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1532_eq, node1533_eq]
  kernel_rfl
theorem node1535_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state17260 33937 state65 = (program42584,state17301,34061) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
