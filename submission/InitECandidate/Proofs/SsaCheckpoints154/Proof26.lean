import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof25
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1664_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2747 state64 453 state65 = (program44585,state19215,38285) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2747
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1662_eq, node1663_eq]
  kernel_rfl
theorem node1665_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2750 state19215 38285 state65 = (program44639,state19258,38401) := by
  kernel_rfl
theorem node1666_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2751 state64 453 state65 = (program44640,state19258,38401) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2751
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1664_eq, node1665_eq]
  kernel_rfl
theorem node1667_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state19258 38401 state65 = (program44649,state19282,38421) := by
  kernel_rfl
theorem node1668_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2752 state64 453 state65 = (program44650,state19282,38421) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2752
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1666_eq, node1667_eq]
  kernel_rfl
theorem node1669_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state19282 38421 state65 = (program44651,state19293,38425) := by
  kernel_rfl
theorem node1670_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2753 state64 453 state65 = (program44652,state19293,38425) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2753
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1668_eq, node1669_eq]
  kernel_rfl
theorem node1671_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state19293 38425 state65 = (program44709,state19334,38549) := by
  kernel_rfl
theorem node1672_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2754 state64 453 state65 = (program44710,state19334,38549) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2754
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1670_eq, node1671_eq]
  kernel_rfl
theorem node1673_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2757 state19334 38549 state65 = (program44764,state19376,38665) := by
  kernel_rfl
theorem node1674_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2758 state64 453 state65 = (program44765,state19376,38665) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2758
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1672_eq, node1673_eq]
  kernel_rfl
theorem node1675_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state19376 38665 state65 = (program44774,state19398,38685) := by
  kernel_rfl
theorem node1676_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2759 state64 453 state65 = (program44775,state19398,38685) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2759
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1674_eq, node1675_eq]
  kernel_rfl
theorem node1677_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state19398 38685 state65 = (program44776,state19408,38689) := by
  kernel_rfl
theorem node1678_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2760 state64 453 state65 = (program44777,state19408,38689) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2760
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1676_eq, node1677_eq]
  kernel_rfl
theorem node1679_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state19408 38689 state65 = (program44834,state19450,38813) := by
  kernel_rfl
theorem node1680_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2761 state64 453 state65 = (program44835,state19450,38813) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2761
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1678_eq, node1679_eq]
  kernel_rfl
theorem node1681_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2764 state19450 38813 state65 = (program44889,state19492,38929) := by
  kernel_rfl
theorem node1682_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2765 state64 453 state65 = (program44890,state19492,38929) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2765
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1680_eq, node1681_eq]
  kernel_rfl
theorem node1683_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state19492 38929 state65 = (program44899,state19518,38949) := by
  kernel_rfl
theorem node1684_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2766 state64 453 state65 = (program44900,state19518,38949) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2766
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1682_eq, node1683_eq]
  kernel_rfl
theorem node1685_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state19518 38949 state65 = (program44901,state19531,38953) := by
  kernel_rfl
theorem node1686_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2767 state64 453 state65 = (program44902,state19531,38953) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2767
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1684_eq, node1685_eq]
  kernel_rfl
theorem node1687_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state19531 38953 state65 = (program44959,state19573,39077) := by
  kernel_rfl
theorem node1688_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2768 state64 453 state65 = (program44960,state19573,39077) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2768
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1686_eq, node1687_eq]
  kernel_rfl
theorem node1689_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2771 state19573 39077 state65 = (program45014,state19613,39193) := by
  kernel_rfl
theorem node1690_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2772 state64 453 state65 = (program45015,state19613,39193) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2772
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1688_eq, node1689_eq]
  kernel_rfl
theorem node1691_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state19613 39193 state65 = (program45024,state19639,39213) := by
  kernel_rfl
theorem node1692_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2773 state64 453 state65 = (program45025,state19639,39213) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2773
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1690_eq, node1691_eq]
  kernel_rfl
theorem node1693_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state19639 39213 state65 = (program45026,state19652,39217) := by
  kernel_rfl
theorem node1694_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2774 state64 453 state65 = (program45027,state19652,39217) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2774
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1692_eq, node1693_eq]
  kernel_rfl
theorem node1695_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state19652 39217 state65 = (program45084,state19695,39341) := by
  kernel_rfl
theorem node1696_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2775 state64 453 state65 = (program45085,state19695,39341) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2775
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1694_eq, node1695_eq]
  kernel_rfl
theorem node1697_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2778 state19695 39341 state65 = (program45139,state19736,39457) := by
  kernel_rfl
theorem node1698_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2779 state64 453 state65 = (program45140,state19736,39457) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2779
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1696_eq, node1697_eq]
  kernel_rfl
theorem node1699_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state19736 39457 state65 = (program45149,state19759,39477) := by
  kernel_rfl
theorem node1700_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2780 state64 453 state65 = (program45150,state19759,39477) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2780
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1698_eq, node1699_eq]
  kernel_rfl
theorem node1701_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state19759 39477 state65 = (program45151,state19771,39481) := by
  kernel_rfl
theorem node1702_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2781 state64 453 state65 = (program45152,state19771,39481) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2781
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1700_eq, node1701_eq]
  kernel_rfl
theorem node1703_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state19771 39481 state65 = (program45209,state19813,39605) := by
  kernel_rfl
theorem node1704_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2782 state64 453 state65 = (program45210,state19813,39605) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2782
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1702_eq, node1703_eq]
  kernel_rfl
theorem node1705_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2785 state19813 39605 state65 = (program45264,state19854,39721) := by
  kernel_rfl
theorem node1706_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2786 state64 453 state65 = (program45265,state19854,39721) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2786
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1704_eq, node1705_eq]
  kernel_rfl
theorem node1707_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state19854 39721 state65 = (program45274,state19877,39741) := by
  kernel_rfl
theorem node1708_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2787 state64 453 state65 = (program45275,state19877,39741) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2787
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1706_eq, node1707_eq]
  kernel_rfl
theorem node1709_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state19877 39741 state65 = (program45276,state19887,39745) := by
  kernel_rfl
theorem node1710_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2788 state64 453 state65 = (program45277,state19887,39745) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2788
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1708_eq, node1709_eq]
  kernel_rfl
theorem node1711_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state19887 39745 state65 = (program45334,state19929,39869) := by
  kernel_rfl
theorem node1712_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2789 state64 453 state65 = (program45335,state19929,39869) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2789
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1710_eq, node1711_eq]
  kernel_rfl
theorem node1713_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2792 state19929 39869 state65 = (program45389,state19971,39985) := by
  kernel_rfl
theorem node1714_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2793 state64 453 state65 = (program45390,state19971,39985) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2793
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1712_eq, node1713_eq]
  kernel_rfl
theorem node1715_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state19971 39985 state65 = (program45399,state19997,40005) := by
  kernel_rfl
theorem node1716_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2794 state64 453 state65 = (program45400,state19997,40005) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2794
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1714_eq, node1715_eq]
  kernel_rfl
theorem node1717_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state19997 40005 state65 = (program45401,state20010,40009) := by
  kernel_rfl
theorem node1718_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2795 state64 453 state65 = (program45402,state20010,40009) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2795
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1716_eq, node1717_eq]
  kernel_rfl
theorem node1719_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state20010 40009 state65 = (program45459,state20050,40133) := by
  kernel_rfl
theorem node1720_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2796 state64 453 state65 = (program45460,state20050,40133) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2796
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1718_eq, node1719_eq]
  kernel_rfl
theorem node1721_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2799 state20050 40133 state65 = (program45514,state20092,40249) := by
  kernel_rfl
theorem node1722_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2800 state64 453 state65 = (program45515,state20092,40249) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2800
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1720_eq, node1721_eq]
  kernel_rfl
theorem node1723_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state20092 40249 state65 = (program45524,state20118,40269) := by
  kernel_rfl
theorem node1724_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2801 state64 453 state65 = (program45525,state20118,40269) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2801
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1722_eq, node1723_eq]
  kernel_rfl
theorem node1725_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state20118 40269 state65 = (program45526,state20131,40273) := by
  kernel_rfl
theorem node1726_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2802 state64 453 state65 = (program45527,state20131,40273) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2802
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1724_eq, node1725_eq]
  kernel_rfl
theorem node1727_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state20131 40273 state65 = (program45584,state20172,40397) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
