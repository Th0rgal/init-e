import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof29
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1920_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2993 state64 453 state65 = (program47038,state22003,43369) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2993
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1918_eq, node1919_eq]
  kernel_rfl
theorem node1921_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2996 state22003 43369 state65 = (program47047,state22027,43389) := by
  kernel_rfl
theorem node1922_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2997 state64 453 state65 = (program47048,state22027,43389) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2997
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1920_eq, node1921_eq]
  kernel_rfl
theorem node1923_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1557 state22027 43389 state65 = (program47049,state22039,43393) := by
  kernel_rfl
theorem node1924_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2998 state64 453 state65 = (program47050,state22039,43393) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2998
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1922_eq, node1923_eq]
  kernel_rfl
theorem node1925_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3000 state22039 43393 state65 = (program47053,state22054,43401) := by
  kernel_rfl
theorem node1926_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3001 state64 453 state65 = (program47054,state22054,43401) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3001
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1924_eq, node1925_eq]
  kernel_rfl
theorem node1927_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3002 state22054 43401 state65 = (program47057,state22069,43409) := by
  kernel_rfl
theorem node1928_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3003 state64 453 state65 = (program47058,state22069,43409) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3003
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1926_eq, node1927_eq]
  kernel_rfl
theorem node1929_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22069 43409 state65 = (program47059,state22069,43409) := by
  kernel_rfl
theorem node1930_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3004 state64 453 state65 = (program47060,state22069,43409) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3004
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1928_eq, node1929_eq]
  kernel_rfl
theorem node1931_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3006 state22069 43409 state65 = (program47063,state22084,43417) := by
  kernel_rfl
theorem node1932_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3007 state64 453 state65 = (program47064,state22084,43417) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3007
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1930_eq, node1931_eq]
  kernel_rfl
theorem node1933_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3008 state22084 43417 state65 = (program47067,state22099,43425) := by
  kernel_rfl
theorem node1934_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3009 state64 453 state65 = (program47068,state22099,43425) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3009
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1932_eq, node1933_eq]
  kernel_rfl
theorem node1935_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22099 43425 state65 = (program47069,state22099,43425) := by
  kernel_rfl
theorem node1936_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3010 state64 453 state65 = (program47070,state22099,43425) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3010
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1934_eq, node1935_eq]
  kernel_rfl
theorem node1937_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3012 state22099 43425 state65 = (program47073,state22114,43433) := by
  kernel_rfl
theorem node1938_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3013 state64 453 state65 = (program47074,state22114,43433) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3013
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1936_eq, node1937_eq]
  kernel_rfl
theorem node1939_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3014 state22114 43433 state65 = (program47077,state22129,43441) := by
  kernel_rfl
theorem node1940_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3015 state64 453 state65 = (program47078,state22129,43441) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3015
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1938_eq, node1939_eq]
  kernel_rfl
theorem node1941_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22129 43441 state65 = (program47079,state22129,43441) := by
  kernel_rfl
theorem node1942_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3016 state64 453 state65 = (program47080,state22129,43441) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3016
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1940_eq, node1941_eq]
  kernel_rfl
theorem node1943_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3018 state22129 43441 state65 = (program47083,state22144,43449) := by
  kernel_rfl
theorem node1944_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3019 state64 453 state65 = (program47084,state22144,43449) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3019
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1942_eq, node1943_eq]
  kernel_rfl
theorem node1945_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3020 state22144 43449 state65 = (program47085,state22152,43453) := by
  kernel_rfl
theorem node1946_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3021 state64 453 state65 = (program47086,state22152,43453) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3021
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1944_eq, node1945_eq]
  kernel_rfl
theorem node1947_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22152 43453 state65 = (program47087,state22152,43453) := by
  kernel_rfl
theorem node1948_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3022 state64 453 state65 = (program47088,state22152,43453) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3022
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1946_eq, node1947_eq]
  kernel_rfl
theorem node1949_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3025 state22152 43453 state65 = (program47097,state22175,43473) := by
  kernel_rfl
theorem node1950_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3026 state64 453 state65 = (program47098,state22175,43473) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3026
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1948_eq, node1949_eq]
  kernel_rfl
theorem node1951_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1604 state22175 43473 state65 = (program47099,state22186,43477) := by
  kernel_rfl
theorem node1952_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3027 state64 453 state65 = (program47100,state22186,43477) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3027
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1950_eq, node1951_eq]
  kernel_rfl
theorem node1953_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3029 state22186 43477 state65 = (program47103,state22201,43485) := by
  kernel_rfl
theorem node1954_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3030 state64 453 state65 = (program47104,state22201,43485) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3030
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1952_eq, node1953_eq]
  kernel_rfl
theorem node1955_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3031 state22201 43485 state65 = (program47107,state22220,43493) := by
  kernel_rfl
theorem node1956_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3032 state64 453 state65 = (program47108,state22220,43493) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3032
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1954_eq, node1955_eq]
  kernel_rfl
theorem node1957_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22220 43493 state65 = (program47109,state22220,43493) := by
  kernel_rfl
theorem node1958_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3033 state64 453 state65 = (program47110,state22220,43493) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3033
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1956_eq, node1957_eq]
  kernel_rfl
theorem node1959_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3035 state22220 43493 state65 = (program47113,state22235,43501) := by
  kernel_rfl
theorem node1960_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3036 state64 453 state65 = (program47114,state22235,43501) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3036
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1958_eq, node1959_eq]
  kernel_rfl
theorem node1961_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3037 state22235 43501 state65 = (program47117,state22254,43509) := by
  kernel_rfl
theorem node1962_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3038 state64 453 state65 = (program47118,state22254,43509) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3038
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1960_eq, node1961_eq]
  kernel_rfl
theorem node1963_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22254 43509 state65 = (program47119,state22254,43509) := by
  kernel_rfl
theorem node1964_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3039 state64 453 state65 = (program47120,state22254,43509) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3039
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1962_eq, node1963_eq]
  kernel_rfl
theorem node1965_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3041 state22254 43509 state65 = (program47123,state22269,43517) := by
  kernel_rfl
theorem node1966_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3042 state64 453 state65 = (program47124,state22269,43517) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3042
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1964_eq, node1965_eq]
  kernel_rfl
theorem node1967_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3043 state22269 43517 state65 = (program47127,state22288,43525) := by
  kernel_rfl
theorem node1968_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3044 state64 453 state65 = (program47128,state22288,43525) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3044
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1966_eq, node1967_eq]
  kernel_rfl
theorem node1969_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22288 43525 state65 = (program47129,state22288,43525) := by
  kernel_rfl
theorem node1970_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3045 state64 453 state65 = (program47130,state22288,43525) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3045
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1968_eq, node1969_eq]
  kernel_rfl
theorem node1971_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3047 state22288 43525 state65 = (program47133,state22303,43533) := by
  kernel_rfl
theorem node1972_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3048 state64 453 state65 = (program47134,state22303,43533) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3048
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1970_eq, node1971_eq]
  kernel_rfl
theorem node1973_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3049 state22303 43533 state65 = (program47135,state22315,43537) := by
  kernel_rfl
theorem node1974_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3050 state64 453 state65 = (program47136,state22315,43537) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3050
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1972_eq, node1973_eq]
  kernel_rfl
theorem node1975_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_1141 state22315 43537 state65 = (program47137,state22315,43537) := by
  kernel_rfl
theorem node1976_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3051 state64 453 state65 = (program47138,state22315,43537) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3051
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1974_eq, node1975_eq]
  kernel_rfl
theorem node1977_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3054 state22315 43537 state65 = (program47147,state22341,43557) := by
  kernel_rfl
theorem node1978_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3055 state64 453 state65 = (program47148,state22341,43557) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3055
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1976_eq, node1977_eq]
  kernel_rfl
theorem node1979_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1651 state22341 43557 state65 = (program47149,state22354,43561) := by
  kernel_rfl
theorem node1980_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3056 state64 453 state65 = (program47150,state22354,43561) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3056
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1978_eq, node1979_eq]
  kernel_rfl
theorem node1981_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3058 state22354 43561 state65 = (program47153,state22369,43569) := by
  kernel_rfl
theorem node1982_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3059 state64 453 state65 = (program47154,state22369,43569) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_3059
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1980_eq, node1981_eq]
  kernel_rfl
theorem node1983_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_3060 state22369 43569 state65 = (program47157,state22385,43577) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
