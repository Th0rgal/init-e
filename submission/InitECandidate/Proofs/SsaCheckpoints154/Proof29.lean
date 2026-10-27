import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof28
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1856_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2928 state64 453 state65 = (program46928,state21649,43189) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2928
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1854_eq, node1855_eq]
  kernel_rfl
theorem node1857_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21649 43189 state65 = (program46929,state21649,43189) := by
  kernel_rfl
theorem node1858_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2929 state64 453 state65 = (program46930,state21649,43189) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2929
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1856_eq, node1857_eq]
  kernel_rfl
theorem node1859_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2931 state21649 43189 state65 = (program46933,state21664,43197) := by
  kernel_rfl
theorem node1860_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2932 state64 453 state65 = (program46934,state21664,43197) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2932
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1858_eq, node1859_eq]
  kernel_rfl
theorem node1861_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2933 state21664 43197 state65 = (program46935,state21677,43201) := by
  kernel_rfl
theorem node1862_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2934 state64 453 state65 = (program46936,state21677,43201) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2934
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1860_eq, node1861_eq]
  kernel_rfl
theorem node1863_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21677 43201 state65 = (program46937,state21677,43201) := by
  kernel_rfl
theorem node1864_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2935 state64 453 state65 = (program46938,state21677,43201) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2935
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1862_eq, node1863_eq]
  kernel_rfl
theorem node1865_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2938 state21677 43201 state65 = (program46947,state21703,43221) := by
  kernel_rfl
theorem node1866_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2939 state64 453 state65 = (program46948,state21703,43221) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2939
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1864_eq, node1865_eq]
  kernel_rfl
theorem node1867_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1457 state21703 43221 state65 = (program46949,state21714,43225) := by
  kernel_rfl
theorem node1868_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2940 state64 453 state65 = (program46950,state21714,43225) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2940
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1866_eq, node1867_eq]
  kernel_rfl
theorem node1869_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2942 state21714 43225 state65 = (program46953,state21729,43233) := by
  kernel_rfl
theorem node1870_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2943 state64 453 state65 = (program46954,state21729,43233) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2943
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1868_eq, node1869_eq]
  kernel_rfl
theorem node1871_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2944 state21729 43233 state65 = (program46957,state21747,43241) := by
  kernel_rfl
theorem node1872_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2945 state64 453 state65 = (program46958,state21747,43241) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2945
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1870_eq, node1871_eq]
  kernel_rfl
theorem node1873_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21747 43241 state65 = (program46959,state21747,43241) := by
  kernel_rfl
theorem node1874_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2946 state64 453 state65 = (program46960,state21747,43241) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2946
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1872_eq, node1873_eq]
  kernel_rfl
theorem node1875_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2948 state21747 43241 state65 = (program46963,state21762,43249) := by
  kernel_rfl
theorem node1876_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2949 state64 453 state65 = (program46964,state21762,43249) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2949
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1874_eq, node1875_eq]
  kernel_rfl
theorem node1877_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2950 state21762 43249 state65 = (program46967,state21780,43257) := by
  kernel_rfl
theorem node1878_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2951 state64 453 state65 = (program46968,state21780,43257) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2951
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1876_eq, node1877_eq]
  kernel_rfl
theorem node1879_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21780 43257 state65 = (program46969,state21780,43257) := by
  kernel_rfl
theorem node1880_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2952 state64 453 state65 = (program46970,state21780,43257) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2952
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1878_eq, node1879_eq]
  kernel_rfl
theorem node1881_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2954 state21780 43257 state65 = (program46973,state21795,43265) := by
  kernel_rfl
theorem node1882_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2955 state64 453 state65 = (program46974,state21795,43265) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2955
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1880_eq, node1881_eq]
  kernel_rfl
theorem node1883_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2956 state21795 43265 state65 = (program46977,state21813,43273) := by
  kernel_rfl
theorem node1884_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2957 state64 453 state65 = (program46978,state21813,43273) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2957
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1882_eq, node1883_eq]
  kernel_rfl
theorem node1885_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21813 43273 state65 = (program46979,state21813,43273) := by
  kernel_rfl
theorem node1886_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2958 state64 453 state65 = (program46980,state21813,43273) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2958
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1884_eq, node1885_eq]
  kernel_rfl
theorem node1887_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2960 state21813 43273 state65 = (program46983,state21828,43281) := by
  kernel_rfl
theorem node1888_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2961 state64 453 state65 = (program46984,state21828,43281) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2961
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1886_eq, node1887_eq]
  kernel_rfl
theorem node1889_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2962 state21828 43281 state65 = (program46985,state21839,43285) := by
  kernel_rfl
theorem node1890_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2963 state64 453 state65 = (program46986,state21839,43285) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2963
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1888_eq, node1889_eq]
  kernel_rfl
theorem node1891_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21839 43285 state65 = (program46987,state21839,43285) := by
  kernel_rfl
theorem node1892_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2964 state64 453 state65 = (program46988,state21839,43285) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2964
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1890_eq, node1891_eq]
  kernel_rfl
theorem node1893_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2967 state21839 43285 state65 = (program46997,state21864,43305) := by
  kernel_rfl
theorem node1894_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2968 state64 453 state65 = (program46998,state21864,43305) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2968
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1892_eq, node1893_eq]
  kernel_rfl
theorem node1895_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1508 state21864 43305 state65 = (program46999,state21873,43309) := by
  kernel_rfl
theorem node1896_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2969 state64 453 state65 = (program47000,state21873,43309) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2969
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1894_eq, node1895_eq]
  kernel_rfl
theorem node1897_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2971 state21873 43309 state65 = (program47003,state21888,43317) := by
  kernel_rfl
theorem node1898_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2972 state64 453 state65 = (program47004,state21888,43317) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2972
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1896_eq, node1897_eq]
  kernel_rfl
theorem node1899_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2973 state21888 43317 state65 = (program47007,state21907,43325) := by
  kernel_rfl
theorem node1900_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2974 state64 453 state65 = (program47008,state21907,43325) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2974
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1898_eq, node1899_eq]
  kernel_rfl
theorem node1901_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21907 43325 state65 = (program47009,state21907,43325) := by
  kernel_rfl
theorem node1902_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2975 state64 453 state65 = (program47010,state21907,43325) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2975
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1900_eq, node1901_eq]
  kernel_rfl
theorem node1903_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2977 state21907 43325 state65 = (program47013,state21922,43333) := by
  kernel_rfl
theorem node1904_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2978 state64 453 state65 = (program47014,state21922,43333) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2978
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1902_eq, node1903_eq]
  kernel_rfl
theorem node1905_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2979 state21922 43333 state65 = (program47017,state21941,43341) := by
  kernel_rfl
theorem node1906_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2980 state64 453 state65 = (program47018,state21941,43341) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2980
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1904_eq, node1905_eq]
  kernel_rfl
theorem node1907_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21941 43341 state65 = (program47019,state21941,43341) := by
  kernel_rfl
theorem node1908_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2981 state64 453 state65 = (program47020,state21941,43341) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2981
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1906_eq, node1907_eq]
  kernel_rfl
theorem node1909_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2983 state21941 43341 state65 = (program47023,state21956,43349) := by
  kernel_rfl
theorem node1910_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2984 state64 453 state65 = (program47024,state21956,43349) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2984
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1908_eq, node1909_eq]
  kernel_rfl
theorem node1911_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2985 state21956 43349 state65 = (program47027,state21975,43357) := by
  kernel_rfl
theorem node1912_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2986 state64 453 state65 = (program47028,state21975,43357) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2986
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1910_eq, node1911_eq]
  kernel_rfl
theorem node1913_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state21975 43357 state65 = (program47029,state21975,43357) := by
  kernel_rfl
theorem node1914_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2987 state64 453 state65 = (program47030,state21975,43357) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2987
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1912_eq, node1913_eq]
  kernel_rfl
theorem node1915_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2989 state21975 43357 state65 = (program47033,state21990,43365) := by
  kernel_rfl
theorem node1916_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2990 state64 453 state65 = (program47034,state21990,43365) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2990
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1914_eq, node1915_eq]
  kernel_rfl
theorem node1917_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2991 state21990 43365 state65 = (program47035,state22003,43369) := by
  kernel_rfl
theorem node1918_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2992 state64 453 state65 = (program47036,state22003,43369) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2992
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1916_eq, node1917_eq]
  kernel_rfl
theorem node1919_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22003 43369 state65 = (program47037,state22003,43369) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
