import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof16
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1088_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state11459 21921 state65 = (program36729,state11467,21925) := by
  kernel_rfl
theorem node1089_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1648 state11405 21789 state65 = (program36730,state11467,21925) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1648
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1087_eq, node1088_eq]
  kernel_rfl
theorem node1090_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state11467 21925 state65 = (program36731,state11475,21929) := by
  kernel_rfl
theorem node1091_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1649 state11405 21789 state65 = (program36732,state11475,21929) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1649
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1089_eq, node1090_eq]
  kernel_rfl
theorem node1092_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2254 state64 453 state65 = (program36733,state11475,21929) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2254
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1084_eq, node1091_eq]
  kernel_rfl
theorem node1093_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1651 state11475 21929 state65 = (program36734,state11488,21933) := by
  kernel_rfl
theorem node1094_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2255 state64 453 state65 = (program36735,state11488,21933) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2255
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1092_eq, node1093_eq]
  kernel_rfl
theorem node1095_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2258 state11488 21933 state65 = (program36796,state11533,22057) := by
  kernel_rfl
theorem node1096_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2259 state64 453 state65 = (program36797,state11533,22057) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2259
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1094_eq, node1095_eq]
  kernel_rfl
theorem node1097_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state11533 22057 state65 = (program36806,state11557,22077) := by
  kernel_rfl
theorem node1098_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2260 state64 453 state65 = (program36807,state11557,22077) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2260
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1096_eq, node1097_eq]
  kernel_rfl
theorem node1099_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state11557 22077 state65 = (program36808,state11568,22081) := by
  kernel_rfl
theorem node1100_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2261 state64 453 state65 = (program36809,state11568,22081) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2261
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1098_eq, node1099_eq]
  kernel_rfl
theorem node1101_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state11568 22081 state65 = (program36870,state11609,22205) := by
  kernel_rfl
theorem node1102_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2262 state64 453 state65 = (program36871,state11609,22205) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2262
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1100_eq, node1101_eq]
  kernel_rfl
theorem node1103_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1691 state11609 22205 state65 = (program36932,state11641,22329) := by
  kernel_rfl
theorem node1104_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1692 state11641 22329 state65 = (program36935,state11661,22337) := by
  kernel_rfl
theorem node1105_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1693 state11609 22205 state65 = (program36936,state11661,22337) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1693
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1103_eq, node1104_eq]
  kernel_rfl
theorem node1106_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state11661 22337 state65 = (program36937,state11669,22341) := by
  kernel_rfl
theorem node1107_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1694 state11609 22205 state65 = (program36938,state11669,22341) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1694
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1105_eq, node1106_eq]
  kernel_rfl
theorem node1108_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state11669 22341 state65 = (program36939,state11677,22345) := by
  kernel_rfl
theorem node1109_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1695 state11609 22205 state65 = (program36940,state11677,22345) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1695
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1107_eq, node1108_eq]
  kernel_rfl
theorem node1110_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2263 state64 453 state65 = (program36941,state11677,22345) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2263
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1102_eq, node1109_eq]
  kernel_rfl
theorem node1111_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1697 state11677 22345 state65 = (program36942,state11690,22349) := by
  kernel_rfl
theorem node1112_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2264 state64 453 state65 = (program36943,state11690,22349) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2264
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1110_eq, node1111_eq]
  kernel_rfl
theorem node1113_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2267 state11690 22349 state65 = (program37004,state11734,22473) := by
  kernel_rfl
theorem node1114_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2268 state64 453 state65 = (program37005,state11734,22473) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2268
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1112_eq, node1113_eq]
  kernel_rfl
theorem node1115_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state11734 22473 state65 = (program37014,state11756,22493) := by
  kernel_rfl
theorem node1116_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2269 state64 453 state65 = (program37015,state11756,22493) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2269
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1114_eq, node1115_eq]
  kernel_rfl
theorem node1117_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state11756 22493 state65 = (program37016,state11766,22497) := by
  kernel_rfl
theorem node1118_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2270 state64 453 state65 = (program37017,state11766,22497) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2270
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1116_eq, node1117_eq]
  kernel_rfl
theorem node1119_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state11766 22497 state65 = (program37078,state11808,22621) := by
  kernel_rfl
theorem node1120_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2271 state64 453 state65 = (program37079,state11808,22621) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2271
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1118_eq, node1119_eq]
  kernel_rfl
theorem node1121_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1736 state11808 22621 state65 = (program37140,state11846,22745) := by
  kernel_rfl
theorem node1122_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1737 state11846 22745 state65 = (program37143,state11864,22753) := by
  kernel_rfl
theorem node1123_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1738 state11808 22621 state65 = (program37144,state11864,22753) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1738
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1121_eq, node1122_eq]
  kernel_rfl
theorem node1124_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state11864 22753 state65 = (program37145,state11872,22757) := by
  kernel_rfl
theorem node1125_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1739 state11808 22621 state65 = (program37146,state11872,22757) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1739
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1123_eq, node1124_eq]
  kernel_rfl
theorem node1126_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state11872 22757 state65 = (program37147,state11880,22761) := by
  kernel_rfl
theorem node1127_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1740 state11808 22621 state65 = (program37148,state11880,22761) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1740
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1125_eq, node1126_eq]
  kernel_rfl
theorem node1128_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2272 state64 453 state65 = (program37149,state11880,22761) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2272
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1120_eq, node1127_eq]
  kernel_rfl
theorem node1129_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1742 state11880 22761 state65 = (program37150,state11891,22765) := by
  kernel_rfl
theorem node1130_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2273 state64 453 state65 = (program37151,state11891,22765) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2273
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1128_eq, node1129_eq]
  kernel_rfl
theorem node1131_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2276 state11891 22765 state65 = (program37212,state11933,22889) := by
  kernel_rfl
theorem node1132_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2277 state64 453 state65 = (program37213,state11933,22889) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2277
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1130_eq, node1131_eq]
  kernel_rfl
theorem node1133_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state11933 22889 state65 = (program37222,state11959,22909) := by
  kernel_rfl
theorem node1134_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2278 state64 453 state65 = (program37223,state11959,22909) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2278
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1132_eq, node1133_eq]
  kernel_rfl
theorem node1135_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state11959 22909 state65 = (program37224,state11972,22913) := by
  kernel_rfl
theorem node1136_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2279 state64 453 state65 = (program37225,state11972,22913) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2279
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1134_eq, node1135_eq]
  kernel_rfl
theorem node1137_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state11972 22913 state65 = (program37286,state12014,23037) := by
  kernel_rfl
theorem node1138_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2280 state64 453 state65 = (program37287,state12014,23037) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2280
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1136_eq, node1137_eq]
  kernel_rfl
theorem node1139_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1781 state12014 23037 state65 = (program37348,state12048,23161) := by
  kernel_rfl
theorem node1140_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1321 state12048 23161 state65 = (program37351,state12068,23169) := by
  kernel_rfl
theorem node1141_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1782 state12014 23037 state65 = (program37352,state12068,23169) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1782
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1139_eq, node1140_eq]
  kernel_rfl
theorem node1142_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state12068 23169 state65 = (program37353,state12076,23173) := by
  kernel_rfl
theorem node1143_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1783 state12014 23037 state65 = (program37354,state12076,23173) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1783
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1141_eq, node1142_eq]
  kernel_rfl
theorem node1144_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state12076 23173 state65 = (program37355,state12084,23177) := by
  kernel_rfl
theorem node1145_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1784 state12014 23037 state65 = (program37356,state12084,23177) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1784
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1143_eq, node1144_eq]
  kernel_rfl
theorem node1146_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2281 state64 453 state65 = (program37357,state12084,23177) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2281
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1138_eq, node1145_eq]
  kernel_rfl
theorem node1147_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1786 state12084 23177 state65 = (program37358,state12097,23181) := by
  kernel_rfl
theorem node1148_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2282 state64 453 state65 = (program37359,state12097,23181) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2282
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1146_eq, node1147_eq]
  kernel_rfl
theorem node1149_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2285 state12097 23181 state65 = (program37420,state12142,23305) := by
  kernel_rfl
theorem node1150_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2286 state64 453 state65 = (program37421,state12142,23305) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2286
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1148_eq, node1149_eq]
  kernel_rfl
theorem node1151_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state12142 23305 state65 = (program37430,state12168,23325) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
