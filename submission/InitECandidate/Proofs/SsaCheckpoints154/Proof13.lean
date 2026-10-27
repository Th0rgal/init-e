import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof12
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node832_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2127 state64 453 state65 = (program33751,state8556,15965) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2127
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node830_eq, node831_eq]
  kernel_rfl
theorem node833_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1736 state8556 15965 state65 = (program33812,state8594,16089) := by
  kernel_rfl
theorem node834_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1737 state8594 16089 state65 = (program33815,state8612,16097) := by
  kernel_rfl
theorem node835_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1738 state8556 15965 state65 = (program33816,state8612,16097) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1738
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node833_eq, node834_eq]
  kernel_rfl
theorem node836_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state8612 16097 state65 = (program33817,state8620,16101) := by
  kernel_rfl
theorem node837_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1739 state8556 15965 state65 = (program33818,state8620,16101) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1739
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node835_eq, node836_eq]
  kernel_rfl
theorem node838_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state8620 16101 state65 = (program33819,state8628,16105) := by
  kernel_rfl
theorem node839_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1740 state8556 15965 state65 = (program33820,state8628,16105) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1740
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node837_eq, node838_eq]
  kernel_rfl
theorem node840_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2128 state64 453 state65 = (program33821,state8628,16105) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2128
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node832_eq, node839_eq]
  kernel_rfl
theorem node841_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1742 state8628 16105 state65 = (program33822,state8639,16109) := by
  kernel_rfl
theorem node842_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2129 state64 453 state65 = (program33823,state8639,16109) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2129
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node840_eq, node841_eq]
  kernel_rfl
theorem node843_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2132 state8639 16109 state65 = (program33884,state8681,16233) := by
  kernel_rfl
theorem node844_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2133 state64 453 state65 = (program33885,state8681,16233) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2133
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node842_eq, node843_eq]
  kernel_rfl
theorem node845_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state8681 16233 state65 = (program33894,state8707,16253) := by
  kernel_rfl
theorem node846_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2134 state64 453 state65 = (program33895,state8707,16253) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2134
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node844_eq, node845_eq]
  kernel_rfl
theorem node847_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state8707 16253 state65 = (program33896,state8720,16257) := by
  kernel_rfl
theorem node848_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2135 state64 453 state65 = (program33897,state8720,16257) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2135
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node846_eq, node847_eq]
  kernel_rfl
theorem node849_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state8720 16257 state65 = (program33958,state8762,16381) := by
  kernel_rfl
theorem node850_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2136 state64 453 state65 = (program33959,state8762,16381) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2136
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node848_eq, node849_eq]
  kernel_rfl
theorem node851_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1781 state8762 16381 state65 = (program34020,state8796,16505) := by
  kernel_rfl
theorem node852_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1321 state8796 16505 state65 = (program34023,state8816,16513) := by
  kernel_rfl
theorem node853_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1782 state8762 16381 state65 = (program34024,state8816,16513) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1782
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node851_eq, node852_eq]
  kernel_rfl
theorem node854_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state8816 16513 state65 = (program34025,state8824,16517) := by
  kernel_rfl
theorem node855_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1783 state8762 16381 state65 = (program34026,state8824,16517) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1783
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node853_eq, node854_eq]
  kernel_rfl
theorem node856_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state8824 16517 state65 = (program34027,state8832,16521) := by
  kernel_rfl
theorem node857_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1784 state8762 16381 state65 = (program34028,state8832,16521) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1784
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node855_eq, node856_eq]
  kernel_rfl
theorem node858_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2137 state64 453 state65 = (program34029,state8832,16521) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2137
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node850_eq, node857_eq]
  kernel_rfl
theorem node859_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1786 state8832 16521 state65 = (program34030,state8845,16525) := by
  kernel_rfl
theorem node860_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2138 state64 453 state65 = (program34031,state8845,16525) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2138
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node858_eq, node859_eq]
  kernel_rfl
theorem node861_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2141 state8845 16525 state65 = (program34092,state8890,16649) := by
  kernel_rfl
theorem node862_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2142 state64 453 state65 = (program34093,state8890,16649) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2142
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node860_eq, node861_eq]
  kernel_rfl
theorem node863_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state8890 16649 state65 = (program34102,state8916,16669) := by
  kernel_rfl
theorem node864_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2143 state64 453 state65 = (program34103,state8916,16669) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2143
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node862_eq, node863_eq]
  kernel_rfl
theorem node865_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state8916 16669 state65 = (program34104,state8929,16673) := by
  kernel_rfl
theorem node866_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2144 state64 453 state65 = (program34105,state8929,16673) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2144
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node864_eq, node865_eq]
  kernel_rfl
theorem node867_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state8929 16673 state65 = (program34166,state8972,16797) := by
  kernel_rfl
theorem node868_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2145 state64 453 state65 = (program34167,state8972,16797) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2145
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node866_eq, node867_eq]
  kernel_rfl
theorem node869_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1825 state8972 16797 state65 = (program34228,state9007,16921) := by
  kernel_rfl
theorem node870_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1380 state9007 16921 state65 = (program34231,state9026,16929) := by
  kernel_rfl
theorem node871_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1826 state8972 16797 state65 = (program34232,state9026,16929) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1826
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node869_eq, node870_eq]
  kernel_rfl
theorem node872_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state9026 16929 state65 = (program34233,state9034,16933) := by
  kernel_rfl
theorem node873_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1827 state8972 16797 state65 = (program34234,state9034,16933) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1827
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node871_eq, node872_eq]
  kernel_rfl
theorem node874_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state9034 16933 state65 = (program34235,state9042,16937) := by
  kernel_rfl
theorem node875_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1828 state8972 16797 state65 = (program34236,state9042,16937) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1828
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node873_eq, node874_eq]
  kernel_rfl
theorem node876_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2146 state64 453 state65 = (program34237,state9042,16937) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2146
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node868_eq, node875_eq]
  kernel_rfl
theorem node877_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1830 state9042 16937 state65 = (program34238,state9054,16941) := by
  kernel_rfl
theorem node878_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2147 state64 453 state65 = (program34239,state9054,16941) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2147
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node876_eq, node877_eq]
  kernel_rfl
theorem node879_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2150 state9054 16941 state65 = (program34300,state9097,17065) := by
  kernel_rfl
theorem node880_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2151 state64 453 state65 = (program34301,state9097,17065) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2151
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node878_eq, node879_eq]
  kernel_rfl
theorem node881_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state9097 17065 state65 = (program34310,state9120,17085) := by
  kernel_rfl
theorem node882_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2152 state64 453 state65 = (program34311,state9120,17085) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2152
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node880_eq, node881_eq]
  kernel_rfl
theorem node883_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state9120 17085 state65 = (program34312,state9132,17089) := by
  kernel_rfl
theorem node884_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2153 state64 453 state65 = (program34313,state9132,17089) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2153
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node882_eq, node883_eq]
  kernel_rfl
theorem node885_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state9132 17089 state65 = (program34374,state9174,17213) := by
  kernel_rfl
theorem node886_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2154 state64 453 state65 = (program34375,state9174,17213) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2154
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node884_eq, node885_eq]
  kernel_rfl
theorem node887_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1869 state9174 17213 state65 = (program34436,state9207,17337) := by
  kernel_rfl
theorem node888_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1432 state9207 17337 state65 = (program34439,state9227,17345) := by
  kernel_rfl
theorem node889_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1870 state9174 17213 state65 = (program34440,state9227,17345) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1870
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node887_eq, node888_eq]
  kernel_rfl
theorem node890_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state9227 17345 state65 = (program34441,state9235,17349) := by
  kernel_rfl
theorem node891_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1871 state9174 17213 state65 = (program34442,state9235,17349) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1871
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node889_eq, node890_eq]
  kernel_rfl
theorem node892_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state9235 17349 state65 = (program34443,state9243,17353) := by
  kernel_rfl
theorem node893_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1872 state9174 17213 state65 = (program34444,state9243,17353) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1872
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node891_eq, node892_eq]
  kernel_rfl
theorem node894_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2155 state64 453 state65 = (program34445,state9243,17353) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2155
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node886_eq, node893_eq]
  kernel_rfl
theorem node895_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1874 state9243 17353 state65 = (program34446,state9256,17357) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
