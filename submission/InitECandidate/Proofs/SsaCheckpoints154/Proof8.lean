import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof7
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node512_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state4955 8609 state65 = (program30073,state4963,8613) := by
  kernel_rfl
theorem node513_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1648 state4901 8477 state65 = (program30074,state4963,8613) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1648
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node511_eq, node512_eq]
  kernel_rfl
theorem node514_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state4963 8613 state65 = (program30075,state4971,8617) := by
  kernel_rfl
theorem node515_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1649 state4901 8477 state65 = (program30076,state4971,8617) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1649
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node513_eq, node514_eq]
  kernel_rfl
theorem node516_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1650 state64 453 state65 = (program30077,state4971,8617) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1650
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node508_eq, node515_eq]
  kernel_rfl
theorem node517_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1651 state4971 8617 state65 = (program30078,state4984,8621) := by
  kernel_rfl
theorem node518_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1652 state64 453 state65 = (program30079,state4984,8621) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1652
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node516_eq, node517_eq]
  kernel_rfl
theorem node519_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1655 state4984 8621 state65 = (program30140,state5029,8745) := by
  kernel_rfl
theorem node520_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1656 state64 453 state65 = (program30141,state5029,8745) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1656
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node518_eq, node519_eq]
  kernel_rfl
theorem node521_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state5029 8745 state65 = (program30150,state5053,8765) := by
  kernel_rfl
theorem node522_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1657 state64 453 state65 = (program30151,state5053,8765) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1657
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node520_eq, node521_eq]
  kernel_rfl
theorem node523_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state5053 8765 state65 = (program30152,state5064,8769) := by
  kernel_rfl
theorem node524_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1658 state64 453 state65 = (program30153,state5064,8769) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1658
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node522_eq, node523_eq]
  kernel_rfl
theorem node525_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state5064 8769 state65 = (program30214,state5105,8893) := by
  kernel_rfl
theorem node526_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1659 state64 453 state65 = (program30215,state5105,8893) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1659
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node524_eq, node525_eq]
  kernel_rfl
theorem node527_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1691 state5105 8893 state65 = (program30276,state5137,9017) := by
  kernel_rfl
theorem node528_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1692 state5137 9017 state65 = (program30279,state5157,9025) := by
  kernel_rfl
theorem node529_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1693 state5105 8893 state65 = (program30280,state5157,9025) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1693
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node527_eq, node528_eq]
  kernel_rfl
theorem node530_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state5157 9025 state65 = (program30281,state5165,9029) := by
  kernel_rfl
theorem node531_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1694 state5105 8893 state65 = (program30282,state5165,9029) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1694
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node529_eq, node530_eq]
  kernel_rfl
theorem node532_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state5165 9029 state65 = (program30283,state5173,9033) := by
  kernel_rfl
theorem node533_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1695 state5105 8893 state65 = (program30284,state5173,9033) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1695
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node531_eq, node532_eq]
  kernel_rfl
theorem node534_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1696 state64 453 state65 = (program30285,state5173,9033) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1696
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node526_eq, node533_eq]
  kernel_rfl
theorem node535_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1697 state5173 9033 state65 = (program30286,state5186,9037) := by
  kernel_rfl
theorem node536_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1698 state64 453 state65 = (program30287,state5186,9037) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1698
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node534_eq, node535_eq]
  kernel_rfl
theorem node537_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1701 state5186 9037 state65 = (program30348,state5230,9161) := by
  kernel_rfl
theorem node538_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1702 state64 453 state65 = (program30349,state5230,9161) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1702
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node536_eq, node537_eq]
  kernel_rfl
theorem node539_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state5230 9161 state65 = (program30358,state5252,9181) := by
  kernel_rfl
theorem node540_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1703 state64 453 state65 = (program30359,state5252,9181) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1703
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node538_eq, node539_eq]
  kernel_rfl
theorem node541_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state5252 9181 state65 = (program30360,state5262,9185) := by
  kernel_rfl
theorem node542_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1704 state64 453 state65 = (program30361,state5262,9185) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1704
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node540_eq, node541_eq]
  kernel_rfl
theorem node543_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state5262 9185 state65 = (program30422,state5304,9309) := by
  kernel_rfl
theorem node544_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1705 state64 453 state65 = (program30423,state5304,9309) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1705
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node542_eq, node543_eq]
  kernel_rfl
theorem node545_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1736 state5304 9309 state65 = (program30484,state5342,9433) := by
  kernel_rfl
theorem node546_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1737 state5342 9433 state65 = (program30487,state5360,9441) := by
  kernel_rfl
theorem node547_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1738 state5304 9309 state65 = (program30488,state5360,9441) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1738
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node545_eq, node546_eq]
  kernel_rfl
theorem node548_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state5360 9441 state65 = (program30489,state5368,9445) := by
  kernel_rfl
theorem node549_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1739 state5304 9309 state65 = (program30490,state5368,9445) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1739
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node547_eq, node548_eq]
  kernel_rfl
theorem node550_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state5368 9445 state65 = (program30491,state5376,9449) := by
  kernel_rfl
theorem node551_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1740 state5304 9309 state65 = (program30492,state5376,9449) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1740
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node549_eq, node550_eq]
  kernel_rfl
theorem node552_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1741 state64 453 state65 = (program30493,state5376,9449) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1741
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node544_eq, node551_eq]
  kernel_rfl
theorem node553_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1742 state5376 9449 state65 = (program30494,state5387,9453) := by
  kernel_rfl
theorem node554_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1743 state64 453 state65 = (program30495,state5387,9453) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1743
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node552_eq, node553_eq]
  kernel_rfl
theorem node555_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1746 state5387 9453 state65 = (program30556,state5429,9577) := by
  kernel_rfl
theorem node556_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1747 state64 453 state65 = (program30557,state5429,9577) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1747
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node554_eq, node555_eq]
  kernel_rfl
theorem node557_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state5429 9577 state65 = (program30566,state5455,9597) := by
  kernel_rfl
theorem node558_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1748 state64 453 state65 = (program30567,state5455,9597) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1748
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node556_eq, node557_eq]
  kernel_rfl
theorem node559_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state5455 9597 state65 = (program30568,state5468,9601) := by
  kernel_rfl
theorem node560_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1749 state64 453 state65 = (program30569,state5468,9601) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1749
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node558_eq, node559_eq]
  kernel_rfl
theorem node561_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state5468 9601 state65 = (program30630,state5510,9725) := by
  kernel_rfl
theorem node562_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1750 state64 453 state65 = (program30631,state5510,9725) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1750
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node560_eq, node561_eq]
  kernel_rfl
theorem node563_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1781 state5510 9725 state65 = (program30692,state5544,9849) := by
  kernel_rfl
theorem node564_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1321 state5544 9849 state65 = (program30695,state5564,9857) := by
  kernel_rfl
theorem node565_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1782 state5510 9725 state65 = (program30696,state5564,9857) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1782
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node563_eq, node564_eq]
  kernel_rfl
theorem node566_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state5564 9857 state65 = (program30697,state5572,9861) := by
  kernel_rfl
theorem node567_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1783 state5510 9725 state65 = (program30698,state5572,9861) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1783
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node565_eq, node566_eq]
  kernel_rfl
theorem node568_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state5572 9861 state65 = (program30699,state5580,9865) := by
  kernel_rfl
theorem node569_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1784 state5510 9725 state65 = (program30700,state5580,9865) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1784
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node567_eq, node568_eq]
  kernel_rfl
theorem node570_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1785 state64 453 state65 = (program30701,state5580,9865) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1785
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node562_eq, node569_eq]
  kernel_rfl
theorem node571_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1786 state5580 9865 state65 = (program30702,state5593,9869) := by
  kernel_rfl
theorem node572_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1787 state64 453 state65 = (program30703,state5593,9869) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1787
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node570_eq, node571_eq]
  kernel_rfl
theorem node573_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1790 state5593 9869 state65 = (program30764,state5638,9993) := by
  kernel_rfl
theorem node574_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1791 state64 453 state65 = (program30765,state5638,9993) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1791
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node572_eq, node573_eq]
  kernel_rfl
theorem node575_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state5638 9993 state65 = (program30774,state5664,10013) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
