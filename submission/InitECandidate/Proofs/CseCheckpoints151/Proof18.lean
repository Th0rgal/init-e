import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof17
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node1152_eq : WordCse.wordCse knowledge576 InitECandidate.Proofs.WordStages.word151_2_11580 = (knowledge577, InitECandidate.Proofs.WordStages.word151_2_11580) := by
  rw [knowledge576_def, knowledge577_def]
  kernel_rfl
theorem node1153_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11581 = (knowledge577, program13885) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1151_eq node1152_eq
theorem node1154_eq : WordCse.wordCse knowledge577 InitECandidate.Proofs.WordStages.word151_2_11582 = (knowledge578, InitECandidate.Proofs.WordStages.word151_2_11582) := by
  rw [knowledge577_def, knowledge578_def]
  kernel_rfl
theorem node1155_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11583 = (knowledge578, program13886) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1153_eq node1154_eq
theorem node1156_eq : WordCse.wordCse knowledge578 InitECandidate.Proofs.WordStages.word151_2_11644 = (knowledge579, program13895) := by
  rw [knowledge578_def, knowledge579_def]
  kernel_rfl
theorem node1157_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11645 = (knowledge579, program13896) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1155_eq node1156_eq
theorem node1158_eq : WordCse.wordCse knowledge579 InitECandidate.Proofs.WordStages.word151_2_11706 = (knowledge580, InitECandidate.Proofs.WordStages.word151_2_11706) := by
  rw [knowledge579_def, knowledge580_def]
  kernel_rfl
theorem node1159_eq : WordCse.wordCse knowledge580 InitECandidate.Proofs.WordStages.word151_2_11709 = (knowledge581, InitECandidate.Proofs.WordStages.word151_2_11709) := by
  rw [knowledge580_def, knowledge581_def]
  kernel_rfl
theorem node1160_eq : WordCse.wordCse knowledge579 InitECandidate.Proofs.WordStages.word151_2_11710 = (knowledge581, InitECandidate.Proofs.WordStages.word151_2_11710) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1158_eq node1159_eq
theorem node1161_eq : WordCse.wordCse knowledge581 InitECandidate.Proofs.WordStages.word151_2_11711 = (knowledge582, InitECandidate.Proofs.WordStages.word151_2_11711) := by
  rw [knowledge581_def, knowledge582_def]
  kernel_rfl
theorem node1162_eq : WordCse.wordCse knowledge579 InitECandidate.Proofs.WordStages.word151_2_11712 = (knowledge582, InitECandidate.Proofs.WordStages.word151_2_11712) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1160_eq node1161_eq
theorem node1163_eq : WordCse.wordCse knowledge582 InitECandidate.Proofs.WordStages.word151_2_11713 = (knowledge583, InitECandidate.Proofs.WordStages.word151_2_11713) := by
  rw [knowledge582_def, knowledge583_def]
  kernel_rfl
theorem node1164_eq : WordCse.wordCse knowledge579 InitECandidate.Proofs.WordStages.word151_2_11714 = (knowledge583, InitECandidate.Proofs.WordStages.word151_2_11714) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1162_eq node1163_eq
theorem node1165_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11715 = (knowledge583, program13897) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1157_eq node1164_eq
theorem node1166_eq : WordCse.wordCse knowledge583 InitECandidate.Proofs.WordStages.word151_2_11716 = (knowledge584, InitECandidate.Proofs.WordStages.word151_2_11716) := by
  rw [knowledge583_def, knowledge584_def]
  kernel_rfl
theorem node1167_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11717 = (knowledge584, program13898) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1165_eq node1166_eq
theorem node1168_eq : WordCse.wordCse knowledge584 InitECandidate.Proofs.WordStages.word151_2_11778 = (knowledge585, InitECandidate.Proofs.WordStages.word151_2_11778) := by
  rw [knowledge584_def, knowledge585_def]
  kernel_rfl
theorem node1169_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11779 = (knowledge585, program13899) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1167_eq node1168_eq
theorem node1170_eq : WordCse.wordCse knowledge585 InitECandidate.Proofs.WordStages.word151_2_11788 = (knowledge586, InitECandidate.Proofs.WordStages.word151_2_11788) := by
  rw [knowledge585_def, knowledge586_def]
  kernel_rfl
theorem node1171_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11789 = (knowledge586, program13900) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1169_eq node1170_eq
theorem node1172_eq : WordCse.wordCse knowledge586 InitECandidate.Proofs.WordStages.word151_2_11790 = (knowledge587, InitECandidate.Proofs.WordStages.word151_2_11790) := by
  rw [knowledge586_def, knowledge587_def]
  kernel_rfl
theorem node1173_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11791 = (knowledge587, program13901) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1171_eq node1172_eq
theorem node1174_eq : WordCse.wordCse knowledge587 InitECandidate.Proofs.WordStages.word151_2_11852 = (knowledge588, program13910) := by
  rw [knowledge587_def, knowledge588_def]
  kernel_rfl
theorem node1175_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11853 = (knowledge588, program13911) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1173_eq node1174_eq
theorem node1176_eq : WordCse.wordCse knowledge588 InitECandidate.Proofs.WordStages.word151_2_11914 = (knowledge589, InitECandidate.Proofs.WordStages.word151_2_11914) := by
  rw [knowledge588_def, knowledge589_def]
  kernel_rfl
theorem node1177_eq : WordCse.wordCse knowledge589 InitECandidate.Proofs.WordStages.word151_2_11917 = (knowledge590, InitECandidate.Proofs.WordStages.word151_2_11917) := by
  rw [knowledge589_def, knowledge590_def]
  kernel_rfl
theorem node1178_eq : WordCse.wordCse knowledge588 InitECandidate.Proofs.WordStages.word151_2_11918 = (knowledge590, InitECandidate.Proofs.WordStages.word151_2_11918) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1176_eq node1177_eq
theorem node1179_eq : WordCse.wordCse knowledge590 InitECandidate.Proofs.WordStages.word151_2_11919 = (knowledge591, InitECandidate.Proofs.WordStages.word151_2_11919) := by
  rw [knowledge590_def, knowledge591_def]
  kernel_rfl
theorem node1180_eq : WordCse.wordCse knowledge588 InitECandidate.Proofs.WordStages.word151_2_11920 = (knowledge591, InitECandidate.Proofs.WordStages.word151_2_11920) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1178_eq node1179_eq
theorem node1181_eq : WordCse.wordCse knowledge591 InitECandidate.Proofs.WordStages.word151_2_11921 = (knowledge592, InitECandidate.Proofs.WordStages.word151_2_11921) := by
  rw [knowledge591_def, knowledge592_def]
  kernel_rfl
theorem node1182_eq : WordCse.wordCse knowledge588 InitECandidate.Proofs.WordStages.word151_2_11922 = (knowledge592, InitECandidate.Proofs.WordStages.word151_2_11922) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1180_eq node1181_eq
theorem node1183_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11923 = (knowledge592, program13912) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1175_eq node1182_eq
theorem node1184_eq : WordCse.wordCse knowledge592 InitECandidate.Proofs.WordStages.word151_2_11924 = (knowledge593, InitECandidate.Proofs.WordStages.word151_2_11924) := by
  rw [knowledge592_def, knowledge593_def]
  kernel_rfl
theorem node1185_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11925 = (knowledge593, program13913) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1183_eq node1184_eq
theorem node1186_eq : WordCse.wordCse knowledge593 InitECandidate.Proofs.WordStages.word151_2_11986 = (knowledge594, InitECandidate.Proofs.WordStages.word151_2_11986) := by
  rw [knowledge593_def, knowledge594_def]
  kernel_rfl
theorem node1187_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11987 = (knowledge594, program13914) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1185_eq node1186_eq
theorem node1188_eq : WordCse.wordCse knowledge594 InitECandidate.Proofs.WordStages.word151_2_11996 = (knowledge595, InitECandidate.Proofs.WordStages.word151_2_11996) := by
  rw [knowledge594_def, knowledge595_def]
  kernel_rfl
theorem node1189_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11997 = (knowledge595, program13915) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1187_eq node1188_eq
theorem node1190_eq : WordCse.wordCse knowledge595 InitECandidate.Proofs.WordStages.word151_2_11998 = (knowledge596, InitECandidate.Proofs.WordStages.word151_2_11998) := by
  rw [knowledge595_def, knowledge596_def]
  kernel_rfl
theorem node1191_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_11999 = (knowledge596, program13916) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1189_eq node1190_eq
theorem node1192_eq : WordCse.wordCse knowledge596 InitECandidate.Proofs.WordStages.word151_2_12060 = (knowledge597, program13925) := by
  rw [knowledge596_def, knowledge597_def]
  kernel_rfl
theorem node1193_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12061 = (knowledge597, program13926) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1191_eq node1192_eq
theorem node1194_eq : WordCse.wordCse knowledge597 InitECandidate.Proofs.WordStages.word151_2_12122 = (knowledge598, InitECandidate.Proofs.WordStages.word151_2_12122) := by
  rw [knowledge597_def, knowledge598_def]
  kernel_rfl
theorem node1195_eq : WordCse.wordCse knowledge598 InitECandidate.Proofs.WordStages.word151_2_12125 = (knowledge599, InitECandidate.Proofs.WordStages.word151_2_12125) := by
  rw [knowledge598_def, knowledge599_def]
  kernel_rfl
theorem node1196_eq : WordCse.wordCse knowledge597 InitECandidate.Proofs.WordStages.word151_2_12126 = (knowledge599, InitECandidate.Proofs.WordStages.word151_2_12126) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1194_eq node1195_eq
theorem node1197_eq : WordCse.wordCse knowledge599 InitECandidate.Proofs.WordStages.word151_2_12127 = (knowledge600, InitECandidate.Proofs.WordStages.word151_2_12127) := by
  rw [knowledge599_def, knowledge600_def]
  kernel_rfl
theorem node1198_eq : WordCse.wordCse knowledge597 InitECandidate.Proofs.WordStages.word151_2_12128 = (knowledge600, InitECandidate.Proofs.WordStages.word151_2_12128) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1196_eq node1197_eq
theorem node1199_eq : WordCse.wordCse knowledge600 InitECandidate.Proofs.WordStages.word151_2_12129 = (knowledge601, InitECandidate.Proofs.WordStages.word151_2_12129) := by
  rw [knowledge600_def, knowledge601_def]
  kernel_rfl
theorem node1200_eq : WordCse.wordCse knowledge597 InitECandidate.Proofs.WordStages.word151_2_12130 = (knowledge601, InitECandidate.Proofs.WordStages.word151_2_12130) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1198_eq node1199_eq
theorem node1201_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12131 = (knowledge601, program13927) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1193_eq node1200_eq
theorem node1202_eq : WordCse.wordCse knowledge601 InitECandidate.Proofs.WordStages.word151_2_12132 = (knowledge602, InitECandidate.Proofs.WordStages.word151_2_12132) := by
  rw [knowledge601_def, knowledge602_def]
  kernel_rfl
theorem node1203_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12133 = (knowledge602, program13928) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1201_eq node1202_eq
theorem node1204_eq : WordCse.wordCse knowledge602 InitECandidate.Proofs.WordStages.word151_2_12194 = (knowledge603, InitECandidate.Proofs.WordStages.word151_2_12194) := by
  rw [knowledge602_def, knowledge603_def]
  kernel_rfl
theorem node1205_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12195 = (knowledge603, program13929) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1203_eq node1204_eq
theorem node1206_eq : WordCse.wordCse knowledge603 InitECandidate.Proofs.WordStages.word151_2_12204 = (knowledge604, InitECandidate.Proofs.WordStages.word151_2_12204) := by
  rw [knowledge603_def, knowledge604_def]
  kernel_rfl
theorem node1207_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12205 = (knowledge604, program13930) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1205_eq node1206_eq
theorem node1208_eq : WordCse.wordCse knowledge604 InitECandidate.Proofs.WordStages.word151_2_12206 = (knowledge605, InitECandidate.Proofs.WordStages.word151_2_12206) := by
  rw [knowledge604_def, knowledge605_def]
  kernel_rfl
theorem node1209_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12207 = (knowledge605, program13931) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1207_eq node1208_eq
theorem node1210_eq : WordCse.wordCse knowledge605 InitECandidate.Proofs.WordStages.word151_2_12268 = (knowledge606, program13940) := by
  rw [knowledge605_def, knowledge606_def]
  kernel_rfl
theorem node1211_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12269 = (knowledge606, program13941) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1209_eq node1210_eq
theorem node1212_eq : WordCse.wordCse knowledge606 InitECandidate.Proofs.WordStages.word151_2_12330 = (knowledge607, InitECandidate.Proofs.WordStages.word151_2_12330) := by
  rw [knowledge606_def, knowledge607_def]
  kernel_rfl
theorem node1213_eq : WordCse.wordCse knowledge607 InitECandidate.Proofs.WordStages.word151_2_12333 = (knowledge608, InitECandidate.Proofs.WordStages.word151_2_12333) := by
  rw [knowledge607_def, knowledge608_def]
  kernel_rfl
theorem node1214_eq : WordCse.wordCse knowledge606 InitECandidate.Proofs.WordStages.word151_2_12334 = (knowledge608, InitECandidate.Proofs.WordStages.word151_2_12334) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1212_eq node1213_eq
theorem node1215_eq : WordCse.wordCse knowledge608 InitECandidate.Proofs.WordStages.word151_2_12335 = (knowledge609, InitECandidate.Proofs.WordStages.word151_2_12335) := by
  rw [knowledge608_def, knowledge609_def]
  kernel_rfl
end InitECandidate.Proofs.CseCheckpoints151
