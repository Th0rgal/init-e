import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof16
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node1088_eq : WordCse.wordCse knowledge543 InitECandidate.Proofs.WordStages.word151_2_10878 = (knowledge545, InitECandidate.Proofs.WordStages.word151_2_10878) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1086_eq node1087_eq
theorem node1089_eq : WordCse.wordCse knowledge545 InitECandidate.Proofs.WordStages.word151_2_10879 = (knowledge546, InitECandidate.Proofs.WordStages.word151_2_10879) := by
  rw [knowledge545_def, knowledge546_def]
  kernel_rfl
theorem node1090_eq : WordCse.wordCse knowledge543 InitECandidate.Proofs.WordStages.word151_2_10880 = (knowledge546, InitECandidate.Proofs.WordStages.word151_2_10880) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1088_eq node1089_eq
theorem node1091_eq : WordCse.wordCse knowledge546 InitECandidate.Proofs.WordStages.word151_2_10881 = (knowledge547, InitECandidate.Proofs.WordStages.word151_2_10881) := by
  rw [knowledge546_def, knowledge547_def]
  kernel_rfl
theorem node1092_eq : WordCse.wordCse knowledge543 InitECandidate.Proofs.WordStages.word151_2_10882 = (knowledge547, InitECandidate.Proofs.WordStages.word151_2_10882) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1090_eq node1091_eq
theorem node1093_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10883 = (knowledge547, program13837) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1085_eq node1092_eq
theorem node1094_eq : WordCse.wordCse knowledge547 InitECandidate.Proofs.WordStages.word151_2_10884 = (knowledge548, InitECandidate.Proofs.WordStages.word151_2_10884) := by
  rw [knowledge547_def, knowledge548_def]
  kernel_rfl
theorem node1095_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10885 = (knowledge548, program13838) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1093_eq node1094_eq
theorem node1096_eq : WordCse.wordCse knowledge548 InitECandidate.Proofs.WordStages.word151_2_10946 = (knowledge549, InitECandidate.Proofs.WordStages.word151_2_10946) := by
  rw [knowledge548_def, knowledge549_def]
  kernel_rfl
theorem node1097_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10947 = (knowledge549, program13839) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1095_eq node1096_eq
theorem node1098_eq : WordCse.wordCse knowledge549 InitECandidate.Proofs.WordStages.word151_2_10956 = (knowledge550, InitECandidate.Proofs.WordStages.word151_2_10956) := by
  rw [knowledge549_def, knowledge550_def]
  kernel_rfl
theorem node1099_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10957 = (knowledge550, program13840) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1097_eq node1098_eq
theorem node1100_eq : WordCse.wordCse knowledge550 InitECandidate.Proofs.WordStages.word151_2_10958 = (knowledge551, InitECandidate.Proofs.WordStages.word151_2_10958) := by
  rw [knowledge550_def, knowledge551_def]
  kernel_rfl
theorem node1101_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10959 = (knowledge551, program13841) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1099_eq node1100_eq
theorem node1102_eq : WordCse.wordCse knowledge551 InitECandidate.Proofs.WordStages.word151_2_11020 = (knowledge552, program13850) := by
  rw [knowledge551_def, knowledge552_def]
  kernel_rfl
theorem node1103_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11021 = (knowledge552, program13851) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1101_eq node1102_eq
theorem node1104_eq : WordCse.wordCse knowledge552 InitECandidate.Proofs.WordStages.word151_2_11082 = (knowledge553, InitECandidate.Proofs.WordStages.word151_2_11082) := by
  rw [knowledge552_def, knowledge553_def]
  kernel_rfl
theorem node1105_eq : WordCse.wordCse knowledge553 InitECandidate.Proofs.WordStages.word151_2_11085 = (knowledge554, InitECandidate.Proofs.WordStages.word151_2_11085) := by
  rw [knowledge553_def, knowledge554_def]
  kernel_rfl
theorem node1106_eq : WordCse.wordCse knowledge552 InitECandidate.Proofs.WordStages.word151_2_11086 = (knowledge554, InitECandidate.Proofs.WordStages.word151_2_11086) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1104_eq node1105_eq
theorem node1107_eq : WordCse.wordCse knowledge554 InitECandidate.Proofs.WordStages.word151_2_11087 = (knowledge555, InitECandidate.Proofs.WordStages.word151_2_11087) := by
  rw [knowledge554_def, knowledge555_def]
  kernel_rfl
theorem node1108_eq : WordCse.wordCse knowledge552 InitECandidate.Proofs.WordStages.word151_2_11088 = (knowledge555, InitECandidate.Proofs.WordStages.word151_2_11088) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1106_eq node1107_eq
theorem node1109_eq : WordCse.wordCse knowledge555 InitECandidate.Proofs.WordStages.word151_2_11089 = (knowledge556, InitECandidate.Proofs.WordStages.word151_2_11089) := by
  rw [knowledge555_def, knowledge556_def]
  kernel_rfl
theorem node1110_eq : WordCse.wordCse knowledge552 InitECandidate.Proofs.WordStages.word151_2_11090 = (knowledge556, InitECandidate.Proofs.WordStages.word151_2_11090) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1108_eq node1109_eq
theorem node1111_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11091 = (knowledge556, program13852) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1103_eq node1110_eq
theorem node1112_eq : WordCse.wordCse knowledge556 InitECandidate.Proofs.WordStages.word151_2_11092 = (knowledge557, InitECandidate.Proofs.WordStages.word151_2_11092) := by
  rw [knowledge556_def, knowledge557_def]
  kernel_rfl
theorem node1113_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11093 = (knowledge557, program13853) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1111_eq node1112_eq
theorem node1114_eq : WordCse.wordCse knowledge557 InitECandidate.Proofs.WordStages.word151_2_11154 = (knowledge558, InitECandidate.Proofs.WordStages.word151_2_11154) := by
  rw [knowledge557_def, knowledge558_def]
  kernel_rfl
theorem node1115_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11155 = (knowledge558, program13854) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1113_eq node1114_eq
theorem node1116_eq : WordCse.wordCse knowledge558 InitECandidate.Proofs.WordStages.word151_2_11164 = (knowledge559, InitECandidate.Proofs.WordStages.word151_2_11164) := by
  rw [knowledge558_def, knowledge559_def]
  kernel_rfl
theorem node1117_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11165 = (knowledge559, program13855) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1115_eq node1116_eq
theorem node1118_eq : WordCse.wordCse knowledge559 InitECandidate.Proofs.WordStages.word151_2_11166 = (knowledge560, InitECandidate.Proofs.WordStages.word151_2_11166) := by
  rw [knowledge559_def, knowledge560_def]
  kernel_rfl
theorem node1119_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11167 = (knowledge560, program13856) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1117_eq node1118_eq
theorem node1120_eq : WordCse.wordCse knowledge560 InitECandidate.Proofs.WordStages.word151_2_11228 = (knowledge561, program13865) := by
  rw [knowledge560_def, knowledge561_def]
  kernel_rfl
theorem node1121_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11229 = (knowledge561, program13866) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1119_eq node1120_eq
theorem node1122_eq : WordCse.wordCse knowledge561 InitECandidate.Proofs.WordStages.word151_2_11290 = (knowledge562, InitECandidate.Proofs.WordStages.word151_2_11290) := by
  rw [knowledge561_def, knowledge562_def]
  kernel_rfl
theorem node1123_eq : WordCse.wordCse knowledge562 InitECandidate.Proofs.WordStages.word151_2_11293 = (knowledge563, InitECandidate.Proofs.WordStages.word151_2_11293) := by
  rw [knowledge562_def, knowledge563_def]
  kernel_rfl
theorem node1124_eq : WordCse.wordCse knowledge561 InitECandidate.Proofs.WordStages.word151_2_11294 = (knowledge563, InitECandidate.Proofs.WordStages.word151_2_11294) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1122_eq node1123_eq
theorem node1125_eq : WordCse.wordCse knowledge563 InitECandidate.Proofs.WordStages.word151_2_11295 = (knowledge564, InitECandidate.Proofs.WordStages.word151_2_11295) := by
  rw [knowledge563_def, knowledge564_def]
  kernel_rfl
theorem node1126_eq : WordCse.wordCse knowledge561 InitECandidate.Proofs.WordStages.word151_2_11296 = (knowledge564, InitECandidate.Proofs.WordStages.word151_2_11296) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1124_eq node1125_eq
theorem node1127_eq : WordCse.wordCse knowledge564 InitECandidate.Proofs.WordStages.word151_2_11297 = (knowledge565, InitECandidate.Proofs.WordStages.word151_2_11297) := by
  rw [knowledge564_def, knowledge565_def]
  kernel_rfl
theorem node1128_eq : WordCse.wordCse knowledge561 InitECandidate.Proofs.WordStages.word151_2_11298 = (knowledge565, InitECandidate.Proofs.WordStages.word151_2_11298) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1126_eq node1127_eq
theorem node1129_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11299 = (knowledge565, program13867) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1121_eq node1128_eq
theorem node1130_eq : WordCse.wordCse knowledge565 InitECandidate.Proofs.WordStages.word151_2_11300 = (knowledge566, InitECandidate.Proofs.WordStages.word151_2_11300) := by
  rw [knowledge565_def, knowledge566_def]
  kernel_rfl
theorem node1131_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11301 = (knowledge566, program13868) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1129_eq node1130_eq
theorem node1132_eq : WordCse.wordCse knowledge566 InitECandidate.Proofs.WordStages.word151_2_11362 = (knowledge567, InitECandidate.Proofs.WordStages.word151_2_11362) := by
  rw [knowledge566_def, knowledge567_def]
  kernel_rfl
theorem node1133_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11363 = (knowledge567, program13869) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1131_eq node1132_eq
theorem node1134_eq : WordCse.wordCse knowledge567 InitECandidate.Proofs.WordStages.word151_2_11372 = (knowledge568, InitECandidate.Proofs.WordStages.word151_2_11372) := by
  rw [knowledge567_def, knowledge568_def]
  kernel_rfl
theorem node1135_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11373 = (knowledge568, program13870) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1133_eq node1134_eq
theorem node1136_eq : WordCse.wordCse knowledge568 InitECandidate.Proofs.WordStages.word151_2_11374 = (knowledge569, InitECandidate.Proofs.WordStages.word151_2_11374) := by
  rw [knowledge568_def, knowledge569_def]
  kernel_rfl
theorem node1137_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11375 = (knowledge569, program13871) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1135_eq node1136_eq
theorem node1138_eq : WordCse.wordCse knowledge569 InitECandidate.Proofs.WordStages.word151_2_11436 = (knowledge570, program13880) := by
  rw [knowledge569_def, knowledge570_def]
  kernel_rfl
theorem node1139_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11437 = (knowledge570, program13881) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1137_eq node1138_eq
theorem node1140_eq : WordCse.wordCse knowledge570 InitECandidate.Proofs.WordStages.word151_2_11498 = (knowledge571, InitECandidate.Proofs.WordStages.word151_2_11498) := by
  rw [knowledge570_def, knowledge571_def]
  kernel_rfl
theorem node1141_eq : WordCse.wordCse knowledge571 InitECandidate.Proofs.WordStages.word151_2_11501 = (knowledge572, InitECandidate.Proofs.WordStages.word151_2_11501) := by
  rw [knowledge571_def, knowledge572_def]
  kernel_rfl
theorem node1142_eq : WordCse.wordCse knowledge570 InitECandidate.Proofs.WordStages.word151_2_11502 = (knowledge572, InitECandidate.Proofs.WordStages.word151_2_11502) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1140_eq node1141_eq
theorem node1143_eq : WordCse.wordCse knowledge572 InitECandidate.Proofs.WordStages.word151_2_11503 = (knowledge573, InitECandidate.Proofs.WordStages.word151_2_11503) := by
  rw [knowledge572_def, knowledge573_def]
  kernel_rfl
theorem node1144_eq : WordCse.wordCse knowledge570 InitECandidate.Proofs.WordStages.word151_2_11504 = (knowledge573, InitECandidate.Proofs.WordStages.word151_2_11504) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1142_eq node1143_eq
theorem node1145_eq : WordCse.wordCse knowledge573 InitECandidate.Proofs.WordStages.word151_2_11505 = (knowledge574, InitECandidate.Proofs.WordStages.word151_2_11505) := by
  rw [knowledge573_def, knowledge574_def]
  kernel_rfl
theorem node1146_eq : WordCse.wordCse knowledge570 InitECandidate.Proofs.WordStages.word151_2_11506 = (knowledge574, InitECandidate.Proofs.WordStages.word151_2_11506) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1144_eq node1145_eq
theorem node1147_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11507 = (knowledge574, program13882) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1139_eq node1146_eq
theorem node1148_eq : WordCse.wordCse knowledge574 InitECandidate.Proofs.WordStages.word151_2_11508 = (knowledge575, InitECandidate.Proofs.WordStages.word151_2_11508) := by
  rw [knowledge574_def, knowledge575_def]
  kernel_rfl
theorem node1149_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11509 = (knowledge575, program13883) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1147_eq node1148_eq
theorem node1150_eq : WordCse.wordCse knowledge575 InitECandidate.Proofs.WordStages.word151_2_11570 = (knowledge576, InitECandidate.Proofs.WordStages.word151_2_11570) := by
  rw [knowledge575_def, knowledge576_def]
  kernel_rfl
theorem node1151_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11571 = (knowledge576, program13884) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1149_eq node1150_eq
end InitECandidate.Proofs.CseCheckpoints151
