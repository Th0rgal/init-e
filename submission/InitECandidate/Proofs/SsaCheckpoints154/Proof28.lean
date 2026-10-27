import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof27
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1792_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2859 state64 453 state65 = (program46585,state21129,42509) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2859
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1790_eq, node1791_eq]
  kernel_rfl
theorem node1793_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2862 state21129 42509 state65 = (program46639,state21172,42625) := by
  kernel_rfl
theorem node1794_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2863 state64 453 state65 = (program46640,state21172,42625) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2863
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1792_eq, node1793_eq]
  kernel_rfl
theorem node1795_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state21172 42625 state65 = (program46649,state21196,42645) := by
  kernel_rfl
theorem node1796_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2864 state64 453 state65 = (program46650,state21196,42645) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2864
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1794_eq, node1795_eq]
  kernel_rfl
theorem node1797_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state21196 42645 state65 = (program46651,state21207,42649) := by
  kernel_rfl
theorem node1798_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2865 state64 453 state65 = (program46652,state21207,42649) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2865
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1796_eq, node1797_eq]
  kernel_rfl
theorem node1799_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state21207 42649 state65 = (program46709,state21248,42773) := by
  kernel_rfl
theorem node1800_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2866 state64 453 state65 = (program46710,state21248,42773) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2866
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1798_eq, node1799_eq]
  kernel_rfl
theorem node1801_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2869 state21248 42773 state65 = (program46766,state21290,42889) := by
  kernel_rfl
theorem node1802_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2870 state64 453 state65 = (program46767,state21290,42889) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2870
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1800_eq, node1801_eq]
  kernel_rfl
theorem node1803_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state21290 42889 state65 = (program46776,state21312,42909) := by
  kernel_rfl
theorem node1804_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2871 state64 453 state65 = (program46777,state21312,42909) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2871
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1802_eq, node1803_eq]
  kernel_rfl
theorem node1805_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state21312 42909 state65 = (program46778,state21322,42913) := by
  kernel_rfl
theorem node1806_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2872 state64 453 state65 = (program46779,state21322,42913) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2872
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1804_eq, node1805_eq]
  kernel_rfl
theorem node1807_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state21322 42913 state65 = (program46839,state21364,43037) := by
  kernel_rfl
theorem node1808_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2873 state64 453 state65 = (program46840,state21364,43037) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2873
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1806_eq, node1807_eq]
  kernel_rfl
theorem node1809_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2876 state21364 43037 state65 = (program46849,state21386,43057) := by
  kernel_rfl
theorem node1810_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2877 state64 453 state65 = (program46850,state21386,43057) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2877
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1808_eq, node1809_eq]
  kernel_rfl
theorem node1811_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1352 state21386 43057 state65 = (program46851,state21396,43061) := by
  kernel_rfl
theorem node1812_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2878 state64 453 state65 = (program46852,state21396,43061) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2878
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1810_eq, node1811_eq]
  kernel_rfl
theorem node1813_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2879 state21396 43061 state65 = (program46853,state21404,43065) := by
  kernel_rfl
theorem node1814_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2880 state64 453 state65 = (program46854,state21404,43065) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2880
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1812_eq, node1813_eq]
  kernel_rfl
theorem node1815_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2882 state21404 43065 state65 = (program46857,state21421,43073) := by
  kernel_rfl
theorem node1816_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2883 state64 453 state65 = (program46858,state21421,43073) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2883
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1814_eq, node1815_eq]
  kernel_rfl
theorem node1817_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21421 43073 state65 = (program46859,state21421,43073) := by
  kernel_rfl
theorem node1818_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2885 state64 453 state65 = (program46860,state21421,43073) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2885
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1816_eq, node1817_eq]
  kernel_rfl
theorem node1819_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2888 state21421 43073 state65 = (program46863,state21436,43081) := by
  kernel_rfl
theorem node1820_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2889 state64 453 state65 = (program46864,state21436,43081) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2889
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1818_eq, node1819_eq]
  kernel_rfl
theorem node1821_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2891 state21436 43081 state65 = (program46867,state21453,43089) := by
  kernel_rfl
theorem node1822_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2892 state64 453 state65 = (program46868,state21453,43089) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2892
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1820_eq, node1821_eq]
  kernel_rfl
theorem node1823_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21453 43089 state65 = (program46869,state21453,43089) := by
  kernel_rfl
theorem node1824_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2893 state64 453 state65 = (program46870,state21453,43089) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2893
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1822_eq, node1823_eq]
  kernel_rfl
theorem node1825_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2895 state21453 43089 state65 = (program46873,state21468,43097) := by
  kernel_rfl
theorem node1826_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2896 state64 453 state65 = (program46874,state21468,43097) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2896
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1824_eq, node1825_eq]
  kernel_rfl
theorem node1827_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2898 state21468 43097 state65 = (program46877,state21485,43105) := by
  kernel_rfl
theorem node1828_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2899 state64 453 state65 = (program46878,state21485,43105) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2899
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1826_eq, node1827_eq]
  kernel_rfl
theorem node1829_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21485 43105 state65 = (program46879,state21485,43105) := by
  kernel_rfl
theorem node1830_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2900 state64 453 state65 = (program46880,state21485,43105) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2900
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1828_eq, node1829_eq]
  kernel_rfl
theorem node1831_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2902 state21485 43105 state65 = (program46883,state21500,43113) := by
  kernel_rfl
theorem node1832_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2903 state64 453 state65 = (program46884,state21500,43113) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2903
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1830_eq, node1831_eq]
  kernel_rfl
theorem node1833_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2904 state21500 43113 state65 = (program46885,state21510,43117) := by
  kernel_rfl
theorem node1834_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2905 state64 453 state65 = (program46886,state21510,43117) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2905
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1832_eq, node1833_eq]
  kernel_rfl
theorem node1835_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21510 43117 state65 = (program46887,state21510,43117) := by
  kernel_rfl
theorem node1836_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2906 state64 453 state65 = (program46888,state21510,43117) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2906
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1834_eq, node1835_eq]
  kernel_rfl
theorem node1837_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2909 state21510 43117 state65 = (program46897,state21536,43137) := by
  kernel_rfl
theorem node1838_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2910 state64 453 state65 = (program46898,state21536,43137) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2910
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1836_eq, node1837_eq]
  kernel_rfl
theorem node1839_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1405 state21536 43137 state65 = (program46899,state21547,43141) := by
  kernel_rfl
theorem node1840_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2911 state64 453 state65 = (program46900,state21547,43141) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2911
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1838_eq, node1839_eq]
  kernel_rfl
theorem node1841_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2913 state21547 43141 state65 = (program46903,state21562,43149) := by
  kernel_rfl
theorem node1842_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2914 state64 453 state65 = (program46904,state21562,43149) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2914
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1840_eq, node1841_eq]
  kernel_rfl
theorem node1843_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2915 state21562 43149 state65 = (program46907,state21581,43157) := by
  kernel_rfl
theorem node1844_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2916 state64 453 state65 = (program46908,state21581,43157) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2916
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1842_eq, node1843_eq]
  kernel_rfl
theorem node1845_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21581 43157 state65 = (program46909,state21581,43157) := by
  kernel_rfl
theorem node1846_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2917 state64 453 state65 = (program46910,state21581,43157) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2917
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1844_eq, node1845_eq]
  kernel_rfl
theorem node1847_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2919 state21581 43157 state65 = (program46913,state21596,43165) := by
  kernel_rfl
theorem node1848_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2920 state64 453 state65 = (program46914,state21596,43165) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2920
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1846_eq, node1847_eq]
  kernel_rfl
theorem node1849_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2921 state21596 43165 state65 = (program46917,state21615,43173) := by
  kernel_rfl
theorem node1850_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2922 state64 453 state65 = (program46918,state21615,43173) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2922
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1848_eq, node1849_eq]
  kernel_rfl
theorem node1851_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21615 43173 state65 = (program46919,state21615,43173) := by
  kernel_rfl
theorem node1852_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2923 state64 453 state65 = (program46920,state21615,43173) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2923
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1850_eq, node1851_eq]
  kernel_rfl
theorem node1853_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2925 state21615 43173 state65 = (program46923,state21630,43181) := by
  kernel_rfl
theorem node1854_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2926 state64 453 state65 = (program46924,state21630,43181) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2926
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1852_eq, node1853_eq]
  kernel_rfl
theorem node1855_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2927 state21630 43181 state65 = (program46927,state21649,43189) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
