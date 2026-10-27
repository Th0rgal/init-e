import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof13
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node896_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2156 state64 453 state65 = (program34447,state9256,17357) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2156
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node894_eq, node895_eq]
  kernel_rfl
theorem node897_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2159 state9256 17357 state65 = (program34508,state9301,17481) := by
  kernel_rfl
theorem node898_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2160 state64 453 state65 = (program34509,state9301,17481) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2160
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node896_eq, node897_eq]
  kernel_rfl
theorem node899_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state9301 17481 state65 = (program34518,state9324,17501) := by
  kernel_rfl
theorem node900_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2161 state64 453 state65 = (program34519,state9324,17501) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2161
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node898_eq, node899_eq]
  kernel_rfl
theorem node901_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state9324 17501 state65 = (program34520,state9334,17505) := by
  kernel_rfl
theorem node902_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2162 state64 453 state65 = (program34521,state9334,17505) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2162
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node900_eq, node901_eq]
  kernel_rfl
theorem node903_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state9334 17505 state65 = (program34582,state9376,17629) := by
  kernel_rfl
theorem node904_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2163 state64 453 state65 = (program34583,state9376,17629) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2163
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node902_eq, node903_eq]
  kernel_rfl
theorem node905_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1913 state9376 17629 state65 = (program34644,state9412,17753) := by
  kernel_rfl
theorem node906_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1483 state9412 17753 state65 = (program34647,state9431,17761) := by
  kernel_rfl
theorem node907_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1914 state9376 17629 state65 = (program34648,state9431,17761) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1914
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node905_eq, node906_eq]
  kernel_rfl
theorem node908_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state9431 17761 state65 = (program34649,state9439,17765) := by
  kernel_rfl
theorem node909_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1915 state9376 17629 state65 = (program34650,state9439,17765) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1915
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node907_eq, node908_eq]
  kernel_rfl
theorem node910_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state9439 17765 state65 = (program34651,state9447,17769) := by
  kernel_rfl
theorem node911_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1916 state9376 17629 state65 = (program34652,state9447,17769) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1916
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node909_eq, node910_eq]
  kernel_rfl
theorem node912_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2164 state64 453 state65 = (program34653,state9447,17769) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2164
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node904_eq, node911_eq]
  kernel_rfl
theorem node913_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1918 state9447 17769 state65 = (program34654,state9459,17773) := by
  kernel_rfl
theorem node914_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2165 state64 453 state65 = (program34655,state9459,17773) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2165
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node912_eq, node913_eq]
  kernel_rfl
theorem node915_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2168 state9459 17773 state65 = (program34716,state9501,17897) := by
  kernel_rfl
theorem node916_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2169 state64 453 state65 = (program34717,state9501,17897) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2169
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node914_eq, node915_eq]
  kernel_rfl
theorem node917_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state9501 17897 state65 = (program34726,state9527,17917) := by
  kernel_rfl
theorem node918_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2170 state64 453 state65 = (program34727,state9527,17917) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2170
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node916_eq, node917_eq]
  kernel_rfl
theorem node919_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state9527 17917 state65 = (program34728,state9540,17921) := by
  kernel_rfl
theorem node920_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2171 state64 453 state65 = (program34729,state9540,17921) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2171
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node918_eq, node919_eq]
  kernel_rfl
theorem node921_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state9540 17921 state65 = (program34790,state9580,18045) := by
  kernel_rfl
theorem node922_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2172 state64 453 state65 = (program34791,state9580,18045) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2172
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node920_eq, node921_eq]
  kernel_rfl
theorem node923_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1956 state9580 18045 state65 = (program34852,state9618,18169) := by
  kernel_rfl
theorem node924_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1532 state9618 18169 state65 = (program34855,state9638,18177) := by
  kernel_rfl
theorem node925_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1957 state9580 18045 state65 = (program34856,state9638,18177) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1957
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node923_eq, node924_eq]
  kernel_rfl
theorem node926_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state9638 18177 state65 = (program34857,state9646,18181) := by
  kernel_rfl
theorem node927_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1958 state9580 18045 state65 = (program34858,state9646,18181) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1958
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node925_eq, node926_eq]
  kernel_rfl
theorem node928_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state9646 18181 state65 = (program34859,state9654,18185) := by
  kernel_rfl
theorem node929_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1959 state9580 18045 state65 = (program34860,state9654,18185) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1959
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node927_eq, node928_eq]
  kernel_rfl
theorem node930_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2173 state64 453 state65 = (program34861,state9654,18185) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2173
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node922_eq, node929_eq]
  kernel_rfl
theorem node931_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1961 state9654 18185 state65 = (program34862,state9667,18189) := by
  kernel_rfl
theorem node932_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2174 state64 453 state65 = (program34863,state9667,18189) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2174
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node930_eq, node931_eq]
  kernel_rfl
theorem node933_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2177 state9667 18189 state65 = (program34924,state9711,18313) := by
  kernel_rfl
theorem node934_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2178 state64 453 state65 = (program34925,state9711,18313) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2178
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node932_eq, node933_eq]
  kernel_rfl
theorem node935_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state9711 18313 state65 = (program34934,state9737,18333) := by
  kernel_rfl
theorem node936_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2179 state64 453 state65 = (program34935,state9737,18333) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2179
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node934_eq, node935_eq]
  kernel_rfl
theorem node937_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state9737 18333 state65 = (program34936,state9750,18337) := by
  kernel_rfl
theorem node938_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2180 state64 453 state65 = (program34937,state9750,18337) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2180
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node936_eq, node937_eq]
  kernel_rfl
theorem node939_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state9750 18337 state65 = (program34998,state9791,18461) := by
  kernel_rfl
theorem node940_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2181 state64 453 state65 = (program34999,state9791,18461) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2181
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node938_eq, node939_eq]
  kernel_rfl
theorem node941_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1999 state9791 18461 state65 = (program35060,state9824,18585) := by
  kernel_rfl
theorem node942_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1579 state9824 18585 state65 = (program35063,state9843,18593) := by
  kernel_rfl
theorem node943_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2000 state9791 18461 state65 = (program35064,state9843,18593) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2000
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node941_eq, node942_eq]
  kernel_rfl
theorem node944_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state9843 18593 state65 = (program35065,state9851,18597) := by
  kernel_rfl
theorem node945_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2001 state9791 18461 state65 = (program35066,state9851,18597) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2001
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node943_eq, node944_eq]
  kernel_rfl
theorem node946_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state9851 18597 state65 = (program35067,state9859,18601) := by
  kernel_rfl
theorem node947_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2002 state9791 18461 state65 = (program35068,state9859,18601) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2002
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node945_eq, node946_eq]
  kernel_rfl
theorem node948_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2182 state64 453 state65 = (program35069,state9859,18601) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2182
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node940_eq, node947_eq]
  kernel_rfl
theorem node949_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2004 state9859 18601 state65 = (program35070,state9871,18605) := by
  kernel_rfl
theorem node950_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2183 state64 453 state65 = (program35071,state9871,18605) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2183
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node948_eq, node949_eq]
  kernel_rfl
theorem node951_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2186 state9871 18605 state65 = (program35132,state9917,18729) := by
  kernel_rfl
theorem node952_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2187 state64 453 state65 = (program35133,state9917,18729) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2187
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node950_eq, node951_eq]
  kernel_rfl
theorem node953_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state9917 18729 state65 = (program35142,state9941,18749) := by
  kernel_rfl
theorem node954_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2188 state64 453 state65 = (program35143,state9941,18749) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2188
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node952_eq, node953_eq]
  kernel_rfl
theorem node955_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state9941 18749 state65 = (program35144,state9952,18753) := by
  kernel_rfl
theorem node956_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2189 state64 453 state65 = (program35145,state9952,18753) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2189
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node954_eq, node955_eq]
  kernel_rfl
theorem node957_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state9952 18753 state65 = (program35206,state9993,18877) := by
  kernel_rfl
theorem node958_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2190 state64 453 state65 = (program35207,state9993,18877) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2190
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node956_eq, node957_eq]
  kernel_rfl
theorem node959_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2042 state9993 18877 state65 = (program35268,state10024,19001) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
