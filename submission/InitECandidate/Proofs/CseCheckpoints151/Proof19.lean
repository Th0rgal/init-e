import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof18
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node1216_eq : WordCse.wordCse knowledge606 InitECandidate.Proofs.WordStages.word151_2_12336 = (knowledge609, InitECandidate.Proofs.WordStages.word151_2_12336) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1214_eq node1215_eq
theorem node1217_eq : WordCse.wordCse knowledge609 InitECandidate.Proofs.WordStages.word151_2_12337 = (knowledge610, InitECandidate.Proofs.WordStages.word151_2_12337) := by
  rw [knowledge609_def, knowledge610_def]
  kernel_rfl
theorem node1218_eq : WordCse.wordCse knowledge606 InitECandidate.Proofs.WordStages.word151_2_12338 = (knowledge610, InitECandidate.Proofs.WordStages.word151_2_12338) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1216_eq node1217_eq
theorem node1219_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12339 = (knowledge610, program13942) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1211_eq node1218_eq
theorem node1220_eq : WordCse.wordCse knowledge610 InitECandidate.Proofs.WordStages.word151_2_12340 = (knowledge611, InitECandidate.Proofs.WordStages.word151_2_12340) := by
  rw [knowledge610_def, knowledge611_def]
  kernel_rfl
theorem node1221_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12341 = (knowledge611, program13943) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1219_eq node1220_eq
theorem node1222_eq : WordCse.wordCse knowledge611 InitECandidate.Proofs.WordStages.word151_2_12402 = (knowledge612, InitECandidate.Proofs.WordStages.word151_2_12402) := by
  rw [knowledge611_def, knowledge612_def]
  kernel_rfl
theorem node1223_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12403 = (knowledge612, program13944) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1221_eq node1222_eq
theorem node1224_eq : WordCse.wordCse knowledge612 InitECandidate.Proofs.WordStages.word151_2_12412 = (knowledge613, InitECandidate.Proofs.WordStages.word151_2_12412) := by
  rw [knowledge612_def, knowledge613_def]
  kernel_rfl
theorem node1225_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12413 = (knowledge613, program13945) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1223_eq node1224_eq
theorem node1226_eq : WordCse.wordCse knowledge613 InitECandidate.Proofs.WordStages.word151_2_12414 = (knowledge614, InitECandidate.Proofs.WordStages.word151_2_12414) := by
  rw [knowledge613_def, knowledge614_def]
  kernel_rfl
theorem node1227_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12415 = (knowledge614, program13946) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1225_eq node1226_eq
theorem node1228_eq : WordCse.wordCse knowledge614 InitECandidate.Proofs.WordStages.word151_2_12476 = (knowledge615, program13955) := by
  rw [knowledge614_def, knowledge615_def]
  kernel_rfl
theorem node1229_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12477 = (knowledge615, program13956) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1227_eq node1228_eq
theorem node1230_eq : WordCse.wordCse knowledge615 InitECandidate.Proofs.WordStages.word151_2_12538 = (knowledge616, InitECandidate.Proofs.WordStages.word151_2_12538) := by
  rw [knowledge615_def, knowledge616_def]
  kernel_rfl
theorem node1231_eq : WordCse.wordCse knowledge616 InitECandidate.Proofs.WordStages.word151_2_12541 = (knowledge617, InitECandidate.Proofs.WordStages.word151_2_12541) := by
  rw [knowledge616_def, knowledge617_def]
  kernel_rfl
theorem node1232_eq : WordCse.wordCse knowledge615 InitECandidate.Proofs.WordStages.word151_2_12542 = (knowledge617, InitECandidate.Proofs.WordStages.word151_2_12542) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1230_eq node1231_eq
theorem node1233_eq : WordCse.wordCse knowledge617 InitECandidate.Proofs.WordStages.word151_2_12543 = (knowledge618, InitECandidate.Proofs.WordStages.word151_2_12543) := by
  rw [knowledge617_def, knowledge618_def]
  kernel_rfl
theorem node1234_eq : WordCse.wordCse knowledge615 InitECandidate.Proofs.WordStages.word151_2_12544 = (knowledge618, InitECandidate.Proofs.WordStages.word151_2_12544) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1232_eq node1233_eq
theorem node1235_eq : WordCse.wordCse knowledge618 InitECandidate.Proofs.WordStages.word151_2_12545 = (knowledge619, InitECandidate.Proofs.WordStages.word151_2_12545) := by
  rw [knowledge618_def, knowledge619_def]
  kernel_rfl
theorem node1236_eq : WordCse.wordCse knowledge615 InitECandidate.Proofs.WordStages.word151_2_12546 = (knowledge619, InitECandidate.Proofs.WordStages.word151_2_12546) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1234_eq node1235_eq
theorem node1237_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12547 = (knowledge619, program13957) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1229_eq node1236_eq
theorem node1238_eq : WordCse.wordCse knowledge619 InitECandidate.Proofs.WordStages.word151_2_12548 = (knowledge620, InitECandidate.Proofs.WordStages.word151_2_12548) := by
  rw [knowledge619_def, knowledge620_def]
  kernel_rfl
theorem node1239_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12549 = (knowledge620, program13958) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1237_eq node1238_eq
theorem node1240_eq : WordCse.wordCse knowledge620 InitECandidate.Proofs.WordStages.word151_2_12610 = (knowledge621, InitECandidate.Proofs.WordStages.word151_2_12610) := by
  rw [knowledge620_def, knowledge621_def]
  kernel_rfl
theorem node1241_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12611 = (knowledge621, program13959) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1239_eq node1240_eq
theorem node1242_eq : WordCse.wordCse knowledge621 InitECandidate.Proofs.WordStages.word151_2_12620 = (knowledge622, InitECandidate.Proofs.WordStages.word151_2_12620) := by
  rw [knowledge621_def, knowledge622_def]
  kernel_rfl
theorem node1243_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12621 = (knowledge622, program13960) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1241_eq node1242_eq
theorem node1244_eq : WordCse.wordCse knowledge622 InitECandidate.Proofs.WordStages.word151_2_12622 = (knowledge623, InitECandidate.Proofs.WordStages.word151_2_12622) := by
  rw [knowledge622_def, knowledge623_def]
  kernel_rfl
theorem node1245_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12623 = (knowledge623, program13961) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1243_eq node1244_eq
theorem node1246_eq : WordCse.wordCse knowledge623 InitECandidate.Proofs.WordStages.word151_2_12684 = (knowledge624, program13970) := by
  rw [knowledge623_def, knowledge624_def]
  kernel_rfl
theorem node1247_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12685 = (knowledge624, program13971) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1245_eq node1246_eq
theorem node1248_eq : WordCse.wordCse knowledge624 InitECandidate.Proofs.WordStages.word151_2_12746 = (knowledge625, InitECandidate.Proofs.WordStages.word151_2_12746) := by
  rw [knowledge624_def, knowledge625_def]
  kernel_rfl
theorem node1249_eq : WordCse.wordCse knowledge625 InitECandidate.Proofs.WordStages.word151_2_12749 = (knowledge626, InitECandidate.Proofs.WordStages.word151_2_12749) := by
  rw [knowledge625_def, knowledge626_def]
  kernel_rfl
theorem node1250_eq : WordCse.wordCse knowledge624 InitECandidate.Proofs.WordStages.word151_2_12750 = (knowledge626, InitECandidate.Proofs.WordStages.word151_2_12750) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1248_eq node1249_eq
theorem node1251_eq : WordCse.wordCse knowledge626 InitECandidate.Proofs.WordStages.word151_2_12751 = (knowledge627, InitECandidate.Proofs.WordStages.word151_2_12751) := by
  rw [knowledge626_def, knowledge627_def]
  kernel_rfl
theorem node1252_eq : WordCse.wordCse knowledge624 InitECandidate.Proofs.WordStages.word151_2_12752 = (knowledge627, InitECandidate.Proofs.WordStages.word151_2_12752) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1250_eq node1251_eq
theorem node1253_eq : WordCse.wordCse knowledge627 InitECandidate.Proofs.WordStages.word151_2_12753 = (knowledge628, InitECandidate.Proofs.WordStages.word151_2_12753) := by
  rw [knowledge627_def, knowledge628_def]
  kernel_rfl
theorem node1254_eq : WordCse.wordCse knowledge624 InitECandidate.Proofs.WordStages.word151_2_12754 = (knowledge628, InitECandidate.Proofs.WordStages.word151_2_12754) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1252_eq node1253_eq
theorem node1255_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12755 = (knowledge628, program13972) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1247_eq node1254_eq
theorem node1256_eq : WordCse.wordCse knowledge628 InitECandidate.Proofs.WordStages.word151_2_12756 = (knowledge629, InitECandidate.Proofs.WordStages.word151_2_12756) := by
  rw [knowledge628_def, knowledge629_def]
  kernel_rfl
theorem node1257_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12757 = (knowledge629, program13973) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1255_eq node1256_eq
theorem node1258_eq : WordCse.wordCse knowledge629 InitECandidate.Proofs.WordStages.word151_2_12818 = (knowledge630, InitECandidate.Proofs.WordStages.word151_2_12818) := by
  rw [knowledge629_def, knowledge630_def]
  kernel_rfl
theorem node1259_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12819 = (knowledge630, program13974) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1257_eq node1258_eq
theorem node1260_eq : WordCse.wordCse knowledge630 InitECandidate.Proofs.WordStages.word151_2_12828 = (knowledge631, InitECandidate.Proofs.WordStages.word151_2_12828) := by
  rw [knowledge630_def, knowledge631_def]
  kernel_rfl
theorem node1261_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12829 = (knowledge631, program13975) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1259_eq node1260_eq
theorem node1262_eq : WordCse.wordCse knowledge631 InitECandidate.Proofs.WordStages.word151_2_12830 = (knowledge632, InitECandidate.Proofs.WordStages.word151_2_12830) := by
  rw [knowledge631_def, knowledge632_def]
  kernel_rfl
theorem node1263_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12831 = (knowledge632, program13976) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1261_eq node1262_eq
theorem node1264_eq : WordCse.wordCse knowledge632 InitECandidate.Proofs.WordStages.word151_2_12892 = (knowledge633, program13985) := by
  rw [knowledge632_def, knowledge633_def]
  kernel_rfl
theorem node1265_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12893 = (knowledge633, program13986) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1263_eq node1264_eq
theorem node1266_eq : WordCse.wordCse knowledge633 InitECandidate.Proofs.WordStages.word151_2_12894 = (knowledge634, InitECandidate.Proofs.WordStages.word151_2_12894) := by
  rw [knowledge633_def, knowledge634_def]
  kernel_rfl
theorem node1267_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12895 = (knowledge634, program13987) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1265_eq node1266_eq
theorem node1268_eq : WordCse.wordCse knowledge634 InitECandidate.Proofs.WordStages.word151_2_12906 = (knowledge635, program13993) := by
  rw [knowledge634_def, knowledge635_def]
  kernel_rfl
theorem node1269_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12907 = (knowledge635, program13994) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1267_eq node1268_eq
theorem node1270_eq : WordCse.wordCse knowledge635 InitECandidate.Proofs.WordStages.word151_2_12908 = (knowledge636, InitECandidate.Proofs.WordStages.word151_2_12908) := by
  rw [knowledge635_def, knowledge636_def]
  kernel_rfl
theorem node1271_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12909 = (knowledge636, program13995) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1269_eq node1270_eq
theorem node1272_eq : WordCse.wordCse knowledge636 InitECandidate.Proofs.WordStages.word151_2_12912 = (knowledge637, InitECandidate.Proofs.WordStages.word151_2_12912) := by
  rw [knowledge636_def, knowledge637_def]
  kernel_rfl
theorem node1273_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12913 = (knowledge637, program13996) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1271_eq node1272_eq
theorem node1274_eq : WordCse.wordCse knowledge637 InitECandidate.Proofs.WordStages.word151_2_12916 = (knowledge638, InitECandidate.Proofs.WordStages.word151_2_12916) := by
  rw [knowledge637_def, knowledge638_def]
  kernel_rfl
theorem node1275_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12917 = (knowledge638, program13997) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1273_eq node1274_eq
theorem node1276_eq : WordCse.wordCse knowledge638 InitECandidate.Proofs.WordStages.word151_2_12928 = (knowledge639, InitECandidate.Proofs.WordStages.word151_2_12928) := by
  rw [knowledge638_def, knowledge639_def]
  kernel_rfl
theorem node1277_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12929 = (knowledge639, program13998) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1275_eq node1276_eq
theorem node1278_eq : WordCse.wordCse knowledge639 InitECandidate.Proofs.WordStages.word151_2_12930 = (knowledge640, InitECandidate.Proofs.WordStages.word151_2_12930) := by
  rw [knowledge639_def, knowledge640_def]
  kernel_rfl
theorem node1279_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_12931 = (knowledge640, program13999) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1277_eq node1278_eq
end InitECandidate.Proofs.CseCheckpoints151
