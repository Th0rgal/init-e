import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof19
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node1280_eq : WordCse.wordCse knowledge640 InitECandidate.Proofs.WordStages.word151_2_12934 = (knowledge641, InitECandidate.Proofs.WordStages.word151_2_12934) := by
  rw [knowledge640_def, knowledge641_def]
  kernel_rfl
theorem node1281_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12935 = (knowledge641, program14000) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1279_eq node1280_eq
theorem node1282_eq : WordCse.wordCse knowledge641 InitECandidate.Proofs.WordStages.word151_2_12938 = (knowledge642, InitECandidate.Proofs.WordStages.word151_2_12938) := by
  rw [knowledge641_def, knowledge642_def]
  kernel_rfl
theorem node1283_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12939 = (knowledge642, program14001) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1281_eq node1282_eq
theorem node1284_eq : WordCse.wordCse knowledge642 InitECandidate.Proofs.WordStages.word151_2_12950 = (knowledge643, InitECandidate.Proofs.WordStages.word151_2_12950) := by
  rw [knowledge642_def, knowledge643_def]
  kernel_rfl
theorem node1285_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12951 = (knowledge643, program14002) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1283_eq node1284_eq
theorem node1286_eq : WordCse.wordCse knowledge643 InitECandidate.Proofs.WordStages.word151_2_12952 = (knowledge644, InitECandidate.Proofs.WordStages.word151_2_12952) := by
  rw [knowledge643_def, knowledge644_def]
  kernel_rfl
theorem node1287_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12953 = (knowledge644, program14003) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1285_eq node1286_eq
theorem node1288_eq : WordCse.wordCse knowledge644 InitECandidate.Proofs.WordStages.word151_2_12956 = (knowledge645, InitECandidate.Proofs.WordStages.word151_2_12956) := by
  rw [knowledge644_def, knowledge645_def]
  kernel_rfl
theorem node1289_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12957 = (knowledge645, program14004) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1287_eq node1288_eq
theorem node1290_eq : WordCse.wordCse knowledge645 InitECandidate.Proofs.WordStages.word151_2_12960 = (knowledge646, InitECandidate.Proofs.WordStages.word151_2_12960) := by
  rw [knowledge645_def, knowledge646_def]
  kernel_rfl
theorem node1291_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12961 = (knowledge646, program14005) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1289_eq node1290_eq
theorem node1292_eq : WordCse.wordCse knowledge646 InitECandidate.Proofs.WordStages.word151_2_12972 = (knowledge647, InitECandidate.Proofs.WordStages.word151_2_12972) := by
  rw [knowledge646_def, knowledge647_def]
  kernel_rfl
theorem node1293_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12973 = (knowledge647, program14006) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1291_eq node1292_eq
theorem node1294_eq : WordCse.wordCse knowledge647 InitECandidate.Proofs.WordStages.word151_2_12974 = (knowledge648, InitECandidate.Proofs.WordStages.word151_2_12974) := by
  rw [knowledge647_def, knowledge648_def]
  kernel_rfl
theorem node1295_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12975 = (knowledge648, program14007) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1293_eq node1294_eq
theorem node1296_eq : WordCse.wordCse knowledge648 InitECandidate.Proofs.WordStages.word151_2_12978 = (knowledge649, InitECandidate.Proofs.WordStages.word151_2_12978) := by
  rw [knowledge648_def, knowledge649_def]
  kernel_rfl
theorem node1297_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12979 = (knowledge649, program14008) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1295_eq node1296_eq
theorem node1298_eq : WordCse.wordCse knowledge649 InitECandidate.Proofs.WordStages.word151_2_12982 = (knowledge650, InitECandidate.Proofs.WordStages.word151_2_12982) := by
  rw [knowledge649_def, knowledge650_def]
  kernel_rfl
theorem node1299_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12983 = (knowledge650, program14009) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1297_eq node1298_eq
theorem node1300_eq : WordCse.wordCse knowledge650 InitECandidate.Proofs.WordStages.word151_2_12994 = (knowledge651, InitECandidate.Proofs.WordStages.word151_2_12994) := by
  rw [knowledge650_def, knowledge651_def]
  kernel_rfl
theorem node1301_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12995 = (knowledge651, program14010) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1299_eq node1300_eq
theorem node1302_eq : WordCse.wordCse knowledge651 InitECandidate.Proofs.WordStages.word151_2_12996 = (knowledge652, InitECandidate.Proofs.WordStages.word151_2_12996) := by
  rw [knowledge651_def, knowledge652_def]
  kernel_rfl
theorem node1303_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12997 = (knowledge652, program14011) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1301_eq node1302_eq
theorem node1304_eq : WordCse.wordCse knowledge652 InitECandidate.Proofs.WordStages.word151_2_13000 = (knowledge653, InitECandidate.Proofs.WordStages.word151_2_13000) := by
  rw [knowledge652_def, knowledge653_def]
  kernel_rfl
theorem node1305_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13001 = (knowledge653, program14012) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1303_eq node1304_eq
theorem node1306_eq : WordCse.wordCse knowledge653 InitECandidate.Proofs.WordStages.word151_2_13004 = (knowledge654, InitECandidate.Proofs.WordStages.word151_2_13004) := by
  rw [knowledge653_def, knowledge654_def]
  kernel_rfl
theorem node1307_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13005 = (knowledge654, program14013) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1305_eq node1306_eq
theorem node1308_eq : WordCse.wordCse knowledge654 InitECandidate.Proofs.WordStages.word151_2_13016 = (knowledge655, InitECandidate.Proofs.WordStages.word151_2_13016) := by
  rw [knowledge654_def, knowledge655_def]
  kernel_rfl
theorem node1309_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13017 = (knowledge655, program14014) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1307_eq node1308_eq
theorem node1310_eq : WordCse.wordCse knowledge655 InitECandidate.Proofs.WordStages.word151_2_13018 = (knowledge656, InitECandidate.Proofs.WordStages.word151_2_13018) := by
  rw [knowledge655_def, knowledge656_def]
  kernel_rfl
theorem node1311_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13019 = (knowledge656, program14015) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1309_eq node1310_eq
theorem node1312_eq : WordCse.wordCse knowledge656 InitECandidate.Proofs.WordStages.word151_2_13022 = (knowledge657, InitECandidate.Proofs.WordStages.word151_2_13022) := by
  rw [knowledge656_def, knowledge657_def]
  kernel_rfl
theorem node1313_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13023 = (knowledge657, program14016) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1311_eq node1312_eq
theorem node1314_eq : WordCse.wordCse knowledge657 InitECandidate.Proofs.WordStages.word151_2_13026 = (knowledge658, InitECandidate.Proofs.WordStages.word151_2_13026) := by
  rw [knowledge657_def, knowledge658_def]
  kernel_rfl
theorem node1315_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13027 = (knowledge658, program14017) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1313_eq node1314_eq
theorem node1316_eq : WordCse.wordCse knowledge658 InitECandidate.Proofs.WordStages.word151_2_13038 = (knowledge659, InitECandidate.Proofs.WordStages.word151_2_13038) := by
  rw [knowledge658_def, knowledge659_def]
  kernel_rfl
theorem node1317_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13039 = (knowledge659, program14018) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1315_eq node1316_eq
theorem node1318_eq : WordCse.wordCse knowledge659 InitECandidate.Proofs.WordStages.word151_2_13040 = (knowledge660, InitECandidate.Proofs.WordStages.word151_2_13040) := by
  rw [knowledge659_def, knowledge660_def]
  kernel_rfl
theorem node1319_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13041 = (knowledge660, program14019) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1317_eq node1318_eq
theorem node1320_eq : WordCse.wordCse knowledge660 InitECandidate.Proofs.WordStages.word151_2_13044 = (knowledge661, InitECandidate.Proofs.WordStages.word151_2_13044) := by
  rw [knowledge660_def, knowledge661_def]
  kernel_rfl
theorem node1321_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13045 = (knowledge661, program14020) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1319_eq node1320_eq
theorem node1322_eq : WordCse.wordCse knowledge661 InitECandidate.Proofs.WordStages.word151_2_13048 = (knowledge662, InitECandidate.Proofs.WordStages.word151_2_13048) := by
  rw [knowledge661_def, knowledge662_def]
  kernel_rfl
theorem node1323_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13049 = (knowledge662, program14021) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1321_eq node1322_eq
theorem node1324_eq : WordCse.wordCse knowledge662 InitECandidate.Proofs.WordStages.word151_2_13060 = (knowledge663, InitECandidate.Proofs.WordStages.word151_2_13060) := by
  rw [knowledge662_def, knowledge663_def]
  kernel_rfl
theorem node1325_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13061 = (knowledge663, program14022) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1323_eq node1324_eq
theorem node1326_eq : WordCse.wordCse knowledge663 InitECandidate.Proofs.WordStages.word151_2_13062 = (knowledge664, InitECandidate.Proofs.WordStages.word151_2_13062) := by
  rw [knowledge663_def, knowledge664_def]
  kernel_rfl
theorem node1327_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13063 = (knowledge664, program14023) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1325_eq node1326_eq
theorem node1328_eq : WordCse.wordCse knowledge664 InitECandidate.Proofs.WordStages.word151_2_13066 = (knowledge665, InitECandidate.Proofs.WordStages.word151_2_13066) := by
  rw [knowledge664_def, knowledge665_def]
  kernel_rfl
theorem node1329_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13067 = (knowledge665, program14024) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1327_eq node1328_eq
theorem node1330_eq : WordCse.wordCse knowledge665 InitECandidate.Proofs.WordStages.word151_2_13068 = (knowledge666, InitECandidate.Proofs.WordStages.word151_2_13068) := by
  rw [knowledge665_def, knowledge666_def]
  kernel_rfl
theorem node1331_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13069 = (knowledge666, program14025) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1329_eq node1330_eq
theorem node1332_eq : WordCse.wordCse knowledge666 InitECandidate.Proofs.WordStages.word151_2_13072 = (knowledge666, InitECandidate.Proofs.WordStages.word151_2_13072) := by
  rw [knowledge666_def]
  kernel_rfl
theorem node1333_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13073 = (knowledge666, program14026) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1331_eq node1332_eq
theorem node1334_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_13074 = (knowledge666, program14027) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node0_eq node1333_eq
end InitECandidate.Proofs.CseCheckpoints151
