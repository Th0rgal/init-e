import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof14
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node960_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1626 state10024 19001 state65 = (program35271,state10044,19009) := by
  kernel_rfl
theorem node961_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2043 state9993 18877 state65 = (program35272,state10044,19009) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2043
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node959_eq, node960_eq]
  kernel_rfl
theorem node962_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state10044 19009 state65 = (program35273,state10052,19013) := by
  kernel_rfl
theorem node963_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2044 state9993 18877 state65 = (program35274,state10052,19013) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2044
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node961_eq, node962_eq]
  kernel_rfl
theorem node964_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state10052 19013 state65 = (program35275,state10060,19017) := by
  kernel_rfl
theorem node965_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2045 state9993 18877 state65 = (program35276,state10060,19017) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2045
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node963_eq, node964_eq]
  kernel_rfl
theorem node966_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2191 state64 453 state65 = (program35277,state10060,19017) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2191
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node958_eq, node965_eq]
  kernel_rfl
theorem node967_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2047 state10060 19017 state65 = (program35278,state10073,19021) := by
  kernel_rfl
theorem node968_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2192 state64 453 state65 = (program35279,state10073,19021) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2192
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node966_eq, node967_eq]
  kernel_rfl
theorem node969_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2195 state10073 19021 state65 = (program35340,state10118,19145) := by
  kernel_rfl
theorem node970_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2196 state64 453 state65 = (program35341,state10118,19145) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2196
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node968_eq, node969_eq]
  kernel_rfl
theorem node971_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state10118 19145 state65 = (program35350,state10140,19165) := by
  kernel_rfl
theorem node972_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2197 state64 453 state65 = (program35351,state10140,19165) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2197
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node970_eq, node971_eq]
  kernel_rfl
theorem node973_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state10140 19165 state65 = (program35352,state10150,19169) := by
  kernel_rfl
theorem node974_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2198 state64 453 state65 = (program35353,state10150,19169) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2198
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node972_eq, node973_eq]
  kernel_rfl
theorem node975_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state10150 19169 state65 = (program35414,state10192,19293) := by
  kernel_rfl
theorem node976_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2199 state64 453 state65 = (program35415,state10192,19293) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2199
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node974_eq, node975_eq]
  kernel_rfl
theorem node977_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1345 state10192 19293 state65 = (program35476,state10232,19417) := by
  kernel_rfl
theorem node978_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1347 state10232 19417 state65 = (program35479,state10249,19425) := by
  kernel_rfl
theorem node979_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1348 state10192 19293 state65 = (program35480,state10249,19425) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1348
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node977_eq, node978_eq]
  kernel_rfl
theorem node980_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state10249 19425 state65 = (program35481,state10257,19429) := by
  kernel_rfl
theorem node981_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1349 state10192 19293 state65 = (program35482,state10257,19429) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1349
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node979_eq, node980_eq]
  kernel_rfl
theorem node982_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state10257 19429 state65 = (program35483,state10265,19433) := by
  kernel_rfl
theorem node983_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1350 state10192 19293 state65 = (program35484,state10265,19433) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1350
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node981_eq, node982_eq]
  kernel_rfl
theorem node984_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2200 state64 453 state65 = (program35485,state10265,19433) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2200
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node976_eq, node983_eq]
  kernel_rfl
theorem node985_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1352 state10265 19433 state65 = (program35486,state10275,19437) := by
  kernel_rfl
theorem node986_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2201 state64 453 state65 = (program35487,state10275,19437) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2201
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node984_eq, node985_eq]
  kernel_rfl
theorem node987_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2204 state10275 19437 state65 = (program35548,state10317,19561) := by
  kernel_rfl
theorem node988_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2205 state64 453 state65 = (program35549,state10317,19561) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2205
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node986_eq, node987_eq]
  kernel_rfl
theorem node989_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state10317 19561 state65 = (program35558,state10343,19581) := by
  kernel_rfl
theorem node990_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2206 state64 453 state65 = (program35559,state10343,19581) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2206
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node988_eq, node989_eq]
  kernel_rfl
theorem node991_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state10343 19581 state65 = (program35560,state10356,19585) := by
  kernel_rfl
theorem node992_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2207 state64 453 state65 = (program35561,state10356,19585) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2207
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node990_eq, node991_eq]
  kernel_rfl
theorem node993_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state10356 19585 state65 = (program35622,state10398,19709) := by
  kernel_rfl
theorem node994_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2208 state64 453 state65 = (program35623,state10398,19709) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2208
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node992_eq, node993_eq]
  kernel_rfl
theorem node995_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1399 state10398 19709 state65 = (program35684,state10434,19833) := by
  kernel_rfl
theorem node996_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1400 state10434 19833 state65 = (program35687,state10452,19841) := by
  kernel_rfl
theorem node997_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1401 state10398 19709 state65 = (program35688,state10452,19841) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1401
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node995_eq, node996_eq]
  kernel_rfl
theorem node998_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state10452 19841 state65 = (program35689,state10460,19845) := by
  kernel_rfl
theorem node999_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1402 state10398 19709 state65 = (program35690,state10460,19845) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1402
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node997_eq, node998_eq]
  kernel_rfl
theorem node1000_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state10460 19845 state65 = (program35691,state10468,19849) := by
  kernel_rfl
theorem node1001_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1403 state10398 19709 state65 = (program35692,state10468,19849) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1403
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node999_eq, node1000_eq]
  kernel_rfl
theorem node1002_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2209 state64 453 state65 = (program35693,state10468,19849) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2209
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node994_eq, node1001_eq]
  kernel_rfl
theorem node1003_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1405 state10468 19849 state65 = (program35694,state10479,19853) := by
  kernel_rfl
theorem node1004_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2210 state64 453 state65 = (program35695,state10479,19853) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2210
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1002_eq, node1003_eq]
  kernel_rfl
theorem node1005_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2213 state10479 19853 state65 = (program35756,state10522,19977) := by
  kernel_rfl
theorem node1006_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2214 state64 453 state65 = (program35757,state10522,19977) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2214
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1004_eq, node1005_eq]
  kernel_rfl
theorem node1007_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state10522 19977 state65 = (program35766,state10548,19997) := by
  kernel_rfl
theorem node1008_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2215 state64 453 state65 = (program35767,state10548,19997) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2215
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1006_eq, node1007_eq]
  kernel_rfl
theorem node1009_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state10548 19997 state65 = (program35768,state10561,20001) := by
  kernel_rfl
theorem node1010_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2216 state64 453 state65 = (program35769,state10561,20001) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2216
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1008_eq, node1009_eq]
  kernel_rfl
theorem node1011_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state10561 20001 state65 = (program35830,state10604,20125) := by
  kernel_rfl
theorem node1012_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2217 state64 453 state65 = (program35831,state10604,20125) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2217
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1010_eq, node1011_eq]
  kernel_rfl
theorem node1013_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1451 state10604 20125 state65 = (program35892,state10641,20249) := by
  kernel_rfl
theorem node1014_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1452 state10641 20249 state65 = (program35895,state10659,20257) := by
  kernel_rfl
theorem node1015_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1453 state10604 20125 state65 = (program35896,state10659,20257) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1453
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1013_eq, node1014_eq]
  kernel_rfl
theorem node1016_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state10659 20257 state65 = (program35897,state10667,20261) := by
  kernel_rfl
theorem node1017_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1454 state10604 20125 state65 = (program35898,state10667,20261) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1454
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1015_eq, node1016_eq]
  kernel_rfl
theorem node1018_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state10667 20261 state65 = (program35899,state10675,20265) := by
  kernel_rfl
theorem node1019_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1455 state10604 20125 state65 = (program35900,state10675,20265) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1455
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1017_eq, node1018_eq]
  kernel_rfl
theorem node1020_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2218 state64 453 state65 = (program35901,state10675,20265) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2218
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1012_eq, node1019_eq]
  kernel_rfl
theorem node1021_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1457 state10675 20265 state65 = (program35902,state10686,20269) := by
  kernel_rfl
theorem node1022_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2219 state64 453 state65 = (program35903,state10686,20269) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2219
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1020_eq, node1021_eq]
  kernel_rfl
theorem node1023_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2222 state10686 20269 state65 = (program35964,state10728,20393) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
