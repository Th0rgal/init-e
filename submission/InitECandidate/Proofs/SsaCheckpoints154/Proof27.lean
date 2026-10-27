import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof26
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1728_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2803 state64 453 state65 = (program45585,state20172,40397) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2803
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1726_eq, node1727_eq]
  kernel_rfl
theorem node1729_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2806 state20172 40397 state65 = (program45639,state20215,40513) := by
  kernel_rfl
theorem node1730_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2807 state64 453 state65 = (program45640,state20215,40513) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2807
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1728_eq, node1729_eq]
  kernel_rfl
theorem node1731_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state20215 40513 state65 = (program45649,state20239,40533) := by
  kernel_rfl
theorem node1732_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2808 state64 453 state65 = (program45650,state20239,40533) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2808
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1730_eq, node1731_eq]
  kernel_rfl
theorem node1733_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state20239 40533 state65 = (program45651,state20250,40537) := by
  kernel_rfl
theorem node1734_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2809 state64 453 state65 = (program45652,state20250,40537) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2809
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1732_eq, node1733_eq]
  kernel_rfl
theorem node1735_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state20250 40537 state65 = (program45709,state20291,40661) := by
  kernel_rfl
theorem node1736_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2810 state64 453 state65 = (program45710,state20291,40661) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2810
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1734_eq, node1735_eq]
  kernel_rfl
theorem node1737_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2813 state20291 40661 state65 = (program45764,state20333,40777) := by
  kernel_rfl
theorem node1738_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2814 state64 453 state65 = (program45765,state20333,40777) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2814
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1736_eq, node1737_eq]
  kernel_rfl
theorem node1739_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state20333 40777 state65 = (program45774,state20355,40797) := by
  kernel_rfl
theorem node1740_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2815 state64 453 state65 = (program45775,state20355,40797) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2815
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1738_eq, node1739_eq]
  kernel_rfl
theorem node1741_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state20355 40797 state65 = (program45776,state20365,40801) := by
  kernel_rfl
theorem node1742_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2816 state64 453 state65 = (program45777,state20365,40801) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2816
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1740_eq, node1741_eq]
  kernel_rfl
theorem node1743_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state20365 40801 state65 = (program45834,state20407,40925) := by
  kernel_rfl
theorem node1744_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2817 state64 453 state65 = (program45835,state20407,40925) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2817
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1742_eq, node1743_eq]
  kernel_rfl
theorem node1745_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2820 state20407 40925 state65 = (program45889,state20449,41041) := by
  kernel_rfl
theorem node1746_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2821 state64 453 state65 = (program45890,state20449,41041) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2821
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1744_eq, node1745_eq]
  kernel_rfl
theorem node1747_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state20449 41041 state65 = (program45899,state20475,41061) := by
  kernel_rfl
theorem node1748_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2822 state64 453 state65 = (program45900,state20475,41061) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2822
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1746_eq, node1747_eq]
  kernel_rfl
theorem node1749_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state20475 41061 state65 = (program45901,state20488,41065) := by
  kernel_rfl
theorem node1750_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2823 state64 453 state65 = (program45902,state20488,41065) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2823
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1748_eq, node1749_eq]
  kernel_rfl
theorem node1751_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state20488 41065 state65 = (program45959,state20530,41189) := by
  kernel_rfl
theorem node1752_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2824 state64 453 state65 = (program45960,state20530,41189) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2824
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1750_eq, node1751_eq]
  kernel_rfl
theorem node1753_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2827 state20530 41189 state65 = (program46014,state20570,41305) := by
  kernel_rfl
theorem node1754_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2828 state64 453 state65 = (program46015,state20570,41305) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2828
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1752_eq, node1753_eq]
  kernel_rfl
theorem node1755_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state20570 41305 state65 = (program46024,state20596,41325) := by
  kernel_rfl
theorem node1756_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2829 state64 453 state65 = (program46025,state20596,41325) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2829
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1754_eq, node1755_eq]
  kernel_rfl
theorem node1757_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state20596 41325 state65 = (program46026,state20609,41329) := by
  kernel_rfl
theorem node1758_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2830 state64 453 state65 = (program46027,state20609,41329) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2830
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1756_eq, node1757_eq]
  kernel_rfl
theorem node1759_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state20609 41329 state65 = (program46084,state20652,41453) := by
  kernel_rfl
theorem node1760_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2831 state64 453 state65 = (program46085,state20652,41453) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2831
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1758_eq, node1759_eq]
  kernel_rfl
theorem node1761_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2834 state20652 41453 state65 = (program46139,state20693,41569) := by
  kernel_rfl
theorem node1762_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2835 state64 453 state65 = (program46140,state20693,41569) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2835
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1760_eq, node1761_eq]
  kernel_rfl
theorem node1763_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state20693 41569 state65 = (program46149,state20716,41589) := by
  kernel_rfl
theorem node1764_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2836 state64 453 state65 = (program46150,state20716,41589) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2836
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1762_eq, node1763_eq]
  kernel_rfl
theorem node1765_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state20716 41589 state65 = (program46151,state20728,41593) := by
  kernel_rfl
theorem node1766_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2837 state64 453 state65 = (program46152,state20728,41593) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2837
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1764_eq, node1765_eq]
  kernel_rfl
theorem node1767_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state20728 41593 state65 = (program46209,state20770,41717) := by
  kernel_rfl
theorem node1768_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2838 state64 453 state65 = (program46210,state20770,41717) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2838
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1766_eq, node1767_eq]
  kernel_rfl
theorem node1769_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2841 state20770 41717 state65 = (program46264,state20811,41833) := by
  kernel_rfl
theorem node1770_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2842 state64 453 state65 = (program46265,state20811,41833) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2842
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1768_eq, node1769_eq]
  kernel_rfl
theorem node1771_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state20811 41833 state65 = (program46274,state20834,41853) := by
  kernel_rfl
theorem node1772_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2843 state64 453 state65 = (program46275,state20834,41853) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2843
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1770_eq, node1771_eq]
  kernel_rfl
theorem node1773_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state20834 41853 state65 = (program46276,state20844,41857) := by
  kernel_rfl
theorem node1774_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2844 state64 453 state65 = (program46277,state20844,41857) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2844
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1772_eq, node1773_eq]
  kernel_rfl
theorem node1775_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state20844 41857 state65 = (program46334,state20886,41981) := by
  kernel_rfl
theorem node1776_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2845 state64 453 state65 = (program46335,state20886,41981) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2845
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1774_eq, node1775_eq]
  kernel_rfl
theorem node1777_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2848 state20886 41981 state65 = (program46389,state20928,42097) := by
  kernel_rfl
theorem node1778_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2849 state64 453 state65 = (program46390,state20928,42097) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2849
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1776_eq, node1777_eq]
  kernel_rfl
theorem node1779_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state20928 42097 state65 = (program46399,state20954,42117) := by
  kernel_rfl
theorem node1780_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2850 state64 453 state65 = (program46400,state20954,42117) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2850
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1778_eq, node1779_eq]
  kernel_rfl
theorem node1781_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state20954 42117 state65 = (program46401,state20967,42121) := by
  kernel_rfl
theorem node1782_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2851 state64 453 state65 = (program46402,state20967,42121) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2851
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1780_eq, node1781_eq]
  kernel_rfl
theorem node1783_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state20967 42121 state65 = (program46459,state21007,42245) := by
  kernel_rfl
theorem node1784_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2852 state64 453 state65 = (program46460,state21007,42245) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2852
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1782_eq, node1783_eq]
  kernel_rfl
theorem node1785_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2855 state21007 42245 state65 = (program46514,state21049,42361) := by
  kernel_rfl
theorem node1786_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2856 state64 453 state65 = (program46515,state21049,42361) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2856
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1784_eq, node1785_eq]
  kernel_rfl
theorem node1787_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state21049 42361 state65 = (program46524,state21075,42381) := by
  kernel_rfl
theorem node1788_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2857 state64 453 state65 = (program46525,state21075,42381) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2857
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1786_eq, node1787_eq]
  kernel_rfl
theorem node1789_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state21075 42381 state65 = (program46526,state21088,42385) := by
  kernel_rfl
theorem node1790_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2858 state64 453 state65 = (program46527,state21088,42385) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2858
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1788_eq, node1789_eq]
  kernel_rfl
theorem node1791_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state21088 42385 state65 = (program46584,state21129,42509) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
