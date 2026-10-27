import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof15
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1024_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2223 state64 453 state65 = (program35965,state10728,20393) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2223
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1022_eq, node1023_eq]
  kernel_rfl
theorem node1025_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state10728 20393 state65 = (program35974,state10751,20413) := by
  kernel_rfl
theorem node1026_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2224 state64 453 state65 = (program35975,state10751,20413) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2224
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1024_eq, node1025_eq]
  kernel_rfl
theorem node1027_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state10751 20413 state65 = (program35976,state10763,20417) := by
  kernel_rfl
theorem node1028_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2225 state64 453 state65 = (program35977,state10763,20417) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2225
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1026_eq, node1027_eq]
  kernel_rfl
theorem node1029_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state10763 20417 state65 = (program36038,state10805,20541) := by
  kernel_rfl
theorem node1030_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2226 state64 453 state65 = (program36039,state10805,20541) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2226
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1028_eq, node1029_eq]
  kernel_rfl
theorem node1031_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1502 state10805 20541 state65 = (program36100,state10837,20665) := by
  kernel_rfl
theorem node1032_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1503 state10837 20665 state65 = (program36103,state10854,20673) := by
  kernel_rfl
theorem node1033_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1504 state10805 20541 state65 = (program36104,state10854,20673) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1504
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1031_eq, node1032_eq]
  kernel_rfl
theorem node1034_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state10854 20673 state65 = (program36105,state10862,20677) := by
  kernel_rfl
theorem node1035_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1505 state10805 20541 state65 = (program36106,state10862,20677) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1505
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1033_eq, node1034_eq]
  kernel_rfl
theorem node1036_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state10862 20677 state65 = (program36107,state10870,20681) := by
  kernel_rfl
theorem node1037_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1506 state10805 20541 state65 = (program36108,state10870,20681) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1506
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1035_eq, node1036_eq]
  kernel_rfl
theorem node1038_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2227 state64 453 state65 = (program36109,state10870,20681) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2227
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1030_eq, node1037_eq]
  kernel_rfl
theorem node1039_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1508 state10870 20681 state65 = (program36110,state10879,20685) := by
  kernel_rfl
theorem node1040_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2228 state64 453 state65 = (program36111,state10879,20685) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2228
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1038_eq, node1039_eq]
  kernel_rfl
theorem node1041_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2231 state10879 20685 state65 = (program36172,state10923,20809) := by
  kernel_rfl
theorem node1042_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2232 state64 453 state65 = (program36173,state10923,20809) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2232
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1040_eq, node1041_eq]
  kernel_rfl
theorem node1043_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state10923 20809 state65 = (program36182,state10946,20829) := by
  kernel_rfl
theorem node1044_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2233 state64 453 state65 = (program36183,state10946,20829) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2233
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1042_eq, node1043_eq]
  kernel_rfl
theorem node1045_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state10946 20829 state65 = (program36184,state10956,20833) := by
  kernel_rfl
theorem node1046_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2234 state64 453 state65 = (program36185,state10956,20833) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2234
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1044_eq, node1045_eq]
  kernel_rfl
theorem node1047_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state10956 20833 state65 = (program36246,state10998,20957) := by
  kernel_rfl
theorem node1048_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2235 state64 453 state65 = (program36247,state10998,20957) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2235
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1046_eq, node1047_eq]
  kernel_rfl
theorem node1049_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1551 state10998 20957 state65 = (program36308,state11033,21081) := by
  kernel_rfl
theorem node1050_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1552 state11033 21081 state65 = (program36311,state11052,21089) := by
  kernel_rfl
theorem node1051_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1553 state10998 20957 state65 = (program36312,state11052,21089) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1553
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1049_eq, node1050_eq]
  kernel_rfl
theorem node1052_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state11052 21089 state65 = (program36313,state11060,21093) := by
  kernel_rfl
theorem node1053_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1554 state10998 20957 state65 = (program36314,state11060,21093) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1554
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1051_eq, node1052_eq]
  kernel_rfl
theorem node1054_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state11060 21093 state65 = (program36315,state11068,21097) := by
  kernel_rfl
theorem node1055_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1555 state10998 20957 state65 = (program36316,state11068,21097) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1555
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1053_eq, node1054_eq]
  kernel_rfl
theorem node1056_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2236 state64 453 state65 = (program36317,state11068,21097) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2236
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1048_eq, node1055_eq]
  kernel_rfl
theorem node1057_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1557 state11068 21097 state65 = (program36318,state11080,21101) := by
  kernel_rfl
theorem node1058_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2237 state64 453 state65 = (program36319,state11080,21101) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2237
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1056_eq, node1057_eq]
  kernel_rfl
theorem node1059_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2240 state11080 21101 state65 = (program36380,state11122,21225) := by
  kernel_rfl
theorem node1060_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2241 state64 453 state65 = (program36381,state11122,21225) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2241
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1058_eq, node1059_eq]
  kernel_rfl
theorem node1061_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state11122 21225 state65 = (program36390,state11148,21245) := by
  kernel_rfl
theorem node1062_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2242 state64 453 state65 = (program36391,state11148,21245) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2242
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1060_eq, node1061_eq]
  kernel_rfl
theorem node1063_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state11148 21245 state65 = (program36392,state11161,21249) := by
  kernel_rfl
theorem node1064_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2243 state64 453 state65 = (program36393,state11161,21249) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2243
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1062_eq, node1063_eq]
  kernel_rfl
theorem node1065_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state11161 21249 state65 = (program36454,state11201,21373) := by
  kernel_rfl
theorem node1066_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2244 state64 453 state65 = (program36455,state11201,21373) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2244
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1064_eq, node1065_eq]
  kernel_rfl
theorem node1067_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1598 state11201 21373 state65 = (program36516,state11237,21497) := by
  kernel_rfl
theorem node1068_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1599 state11237 21497 state65 = (program36519,state11255,21505) := by
  kernel_rfl
theorem node1069_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1600 state11201 21373 state65 = (program36520,state11255,21505) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1600
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1067_eq, node1068_eq]
  kernel_rfl
theorem node1070_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state11255 21505 state65 = (program36521,state11263,21509) := by
  kernel_rfl
theorem node1071_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1601 state11201 21373 state65 = (program36522,state11263,21509) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1601
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1069_eq, node1070_eq]
  kernel_rfl
theorem node1072_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state11263 21509 state65 = (program36523,state11271,21513) := by
  kernel_rfl
theorem node1073_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1602 state11201 21373 state65 = (program36524,state11271,21513) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1602
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1071_eq, node1072_eq]
  kernel_rfl
theorem node1074_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2245 state64 453 state65 = (program36525,state11271,21513) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2245
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1066_eq, node1073_eq]
  kernel_rfl
theorem node1075_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1604 state11271 21513 state65 = (program36526,state11282,21517) := by
  kernel_rfl
theorem node1076_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2246 state64 453 state65 = (program36527,state11282,21517) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2246
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1074_eq, node1075_eq]
  kernel_rfl
theorem node1077_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2249 state11282 21517 state65 = (program36588,state11325,21641) := by
  kernel_rfl
theorem node1078_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2250 state64 453 state65 = (program36589,state11325,21641) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2250
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1076_eq, node1077_eq]
  kernel_rfl
theorem node1079_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state11325 21641 state65 = (program36598,state11351,21661) := by
  kernel_rfl
theorem node1080_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2251 state64 453 state65 = (program36599,state11351,21661) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2251
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1078_eq, node1079_eq]
  kernel_rfl
theorem node1081_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state11351 21661 state65 = (program36600,state11364,21665) := by
  kernel_rfl
theorem node1082_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2252 state64 453 state65 = (program36601,state11364,21665) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2252
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1080_eq, node1081_eq]
  kernel_rfl
theorem node1083_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state11364 21665 state65 = (program36662,state11405,21789) := by
  kernel_rfl
theorem node1084_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2253 state64 453 state65 = (program36663,state11405,21789) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2253
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1082_eq, node1083_eq]
  kernel_rfl
theorem node1085_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1645 state11405 21789 state65 = (program36724,state11439,21913) := by
  kernel_rfl
theorem node1086_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1646 state11439 21913 state65 = (program36727,state11459,21921) := by
  kernel_rfl
theorem node1087_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1647 state11405 21789 state65 = (program36728,state11459,21921) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1647
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1085_eq, node1086_eq]
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
