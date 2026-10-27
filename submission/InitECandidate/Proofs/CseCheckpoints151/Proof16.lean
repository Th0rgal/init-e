import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof15
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node1024_eq : WordCse.wordCse knowledge512 InitECandidate.Proofs.WordStages.word151_2_10114 = (knowledge513, InitECandidate.Proofs.WordStages.word151_2_10114) := by
  rw [knowledge512_def, knowledge513_def]
  kernel_rfl
theorem node1025_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10115 = (knowledge513, program13779) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1023_eq node1024_eq
theorem node1026_eq : WordCse.wordCse knowledge513 InitECandidate.Proofs.WordStages.word151_2_10124 = (knowledge514, InitECandidate.Proofs.WordStages.word151_2_10124) := by
  rw [knowledge513_def, knowledge514_def]
  kernel_rfl
theorem node1027_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10125 = (knowledge514, program13780) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1025_eq node1026_eq
theorem node1028_eq : WordCse.wordCse knowledge514 InitECandidate.Proofs.WordStages.word151_2_10126 = (knowledge515, InitECandidate.Proofs.WordStages.word151_2_10126) := by
  rw [knowledge514_def, knowledge515_def]
  kernel_rfl
theorem node1029_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10127 = (knowledge515, program13781) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1027_eq node1028_eq
theorem node1030_eq : WordCse.wordCse knowledge515 InitECandidate.Proofs.WordStages.word151_2_10188 = (knowledge516, program13790) := by
  rw [knowledge515_def, knowledge516_def]
  kernel_rfl
theorem node1031_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10189 = (knowledge516, program13791) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1029_eq node1030_eq
theorem node1032_eq : WordCse.wordCse knowledge516 InitECandidate.Proofs.WordStages.word151_2_10250 = (knowledge517, InitECandidate.Proofs.WordStages.word151_2_10250) := by
  rw [knowledge516_def, knowledge517_def]
  kernel_rfl
theorem node1033_eq : WordCse.wordCse knowledge517 InitECandidate.Proofs.WordStages.word151_2_10253 = (knowledge518, InitECandidate.Proofs.WordStages.word151_2_10253) := by
  rw [knowledge517_def, knowledge518_def]
  kernel_rfl
theorem node1034_eq : WordCse.wordCse knowledge516 InitECandidate.Proofs.WordStages.word151_2_10254 = (knowledge518, InitECandidate.Proofs.WordStages.word151_2_10254) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1032_eq node1033_eq
theorem node1035_eq : WordCse.wordCse knowledge518 InitECandidate.Proofs.WordStages.word151_2_10255 = (knowledge519, InitECandidate.Proofs.WordStages.word151_2_10255) := by
  rw [knowledge518_def, knowledge519_def]
  kernel_rfl
theorem node1036_eq : WordCse.wordCse knowledge516 InitECandidate.Proofs.WordStages.word151_2_10256 = (knowledge519, InitECandidate.Proofs.WordStages.word151_2_10256) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1034_eq node1035_eq
theorem node1037_eq : WordCse.wordCse knowledge519 InitECandidate.Proofs.WordStages.word151_2_10257 = (knowledge520, InitECandidate.Proofs.WordStages.word151_2_10257) := by
  rw [knowledge519_def, knowledge520_def]
  kernel_rfl
theorem node1038_eq : WordCse.wordCse knowledge516 InitECandidate.Proofs.WordStages.word151_2_10258 = (knowledge520, InitECandidate.Proofs.WordStages.word151_2_10258) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1036_eq node1037_eq
theorem node1039_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10259 = (knowledge520, program13792) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1031_eq node1038_eq
theorem node1040_eq : WordCse.wordCse knowledge520 InitECandidate.Proofs.WordStages.word151_2_10260 = (knowledge521, InitECandidate.Proofs.WordStages.word151_2_10260) := by
  rw [knowledge520_def, knowledge521_def]
  kernel_rfl
theorem node1041_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10261 = (knowledge521, program13793) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1039_eq node1040_eq
theorem node1042_eq : WordCse.wordCse knowledge521 InitECandidate.Proofs.WordStages.word151_2_10322 = (knowledge522, InitECandidate.Proofs.WordStages.word151_2_10322) := by
  rw [knowledge521_def, knowledge522_def]
  kernel_rfl
theorem node1043_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10323 = (knowledge522, program13794) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1041_eq node1042_eq
theorem node1044_eq : WordCse.wordCse knowledge522 InitECandidate.Proofs.WordStages.word151_2_10332 = (knowledge523, InitECandidate.Proofs.WordStages.word151_2_10332) := by
  rw [knowledge522_def, knowledge523_def]
  kernel_rfl
theorem node1045_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10333 = (knowledge523, program13795) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1043_eq node1044_eq
theorem node1046_eq : WordCse.wordCse knowledge523 InitECandidate.Proofs.WordStages.word151_2_10334 = (knowledge524, InitECandidate.Proofs.WordStages.word151_2_10334) := by
  rw [knowledge523_def, knowledge524_def]
  kernel_rfl
theorem node1047_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10335 = (knowledge524, program13796) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1045_eq node1046_eq
theorem node1048_eq : WordCse.wordCse knowledge524 InitECandidate.Proofs.WordStages.word151_2_10396 = (knowledge525, program13805) := by
  rw [knowledge524_def, knowledge525_def]
  kernel_rfl
theorem node1049_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10397 = (knowledge525, program13806) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1047_eq node1048_eq
theorem node1050_eq : WordCse.wordCse knowledge525 InitECandidate.Proofs.WordStages.word151_2_10458 = (knowledge526, InitECandidate.Proofs.WordStages.word151_2_10458) := by
  rw [knowledge525_def, knowledge526_def]
  kernel_rfl
theorem node1051_eq : WordCse.wordCse knowledge526 InitECandidate.Proofs.WordStages.word151_2_10461 = (knowledge527, InitECandidate.Proofs.WordStages.word151_2_10461) := by
  rw [knowledge526_def, knowledge527_def]
  kernel_rfl
theorem node1052_eq : WordCse.wordCse knowledge525 InitECandidate.Proofs.WordStages.word151_2_10462 = (knowledge527, InitECandidate.Proofs.WordStages.word151_2_10462) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1050_eq node1051_eq
theorem node1053_eq : WordCse.wordCse knowledge527 InitECandidate.Proofs.WordStages.word151_2_10463 = (knowledge528, InitECandidate.Proofs.WordStages.word151_2_10463) := by
  rw [knowledge527_def, knowledge528_def]
  kernel_rfl
theorem node1054_eq : WordCse.wordCse knowledge525 InitECandidate.Proofs.WordStages.word151_2_10464 = (knowledge528, InitECandidate.Proofs.WordStages.word151_2_10464) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1052_eq node1053_eq
theorem node1055_eq : WordCse.wordCse knowledge528 InitECandidate.Proofs.WordStages.word151_2_10465 = (knowledge529, InitECandidate.Proofs.WordStages.word151_2_10465) := by
  rw [knowledge528_def, knowledge529_def]
  kernel_rfl
theorem node1056_eq : WordCse.wordCse knowledge525 InitECandidate.Proofs.WordStages.word151_2_10466 = (knowledge529, InitECandidate.Proofs.WordStages.word151_2_10466) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1054_eq node1055_eq
theorem node1057_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10467 = (knowledge529, program13807) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1049_eq node1056_eq
theorem node1058_eq : WordCse.wordCse knowledge529 InitECandidate.Proofs.WordStages.word151_2_10468 = (knowledge530, InitECandidate.Proofs.WordStages.word151_2_10468) := by
  rw [knowledge529_def, knowledge530_def]
  kernel_rfl
theorem node1059_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10469 = (knowledge530, program13808) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1057_eq node1058_eq
theorem node1060_eq : WordCse.wordCse knowledge530 InitECandidate.Proofs.WordStages.word151_2_10530 = (knowledge531, InitECandidate.Proofs.WordStages.word151_2_10530) := by
  rw [knowledge530_def, knowledge531_def]
  kernel_rfl
theorem node1061_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10531 = (knowledge531, program13809) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1059_eq node1060_eq
theorem node1062_eq : WordCse.wordCse knowledge531 InitECandidate.Proofs.WordStages.word151_2_10540 = (knowledge532, InitECandidate.Proofs.WordStages.word151_2_10540) := by
  rw [knowledge531_def, knowledge532_def]
  kernel_rfl
theorem node1063_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10541 = (knowledge532, program13810) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1061_eq node1062_eq
theorem node1064_eq : WordCse.wordCse knowledge532 InitECandidate.Proofs.WordStages.word151_2_10542 = (knowledge533, InitECandidate.Proofs.WordStages.word151_2_10542) := by
  rw [knowledge532_def, knowledge533_def]
  kernel_rfl
theorem node1065_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10543 = (knowledge533, program13811) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1063_eq node1064_eq
theorem node1066_eq : WordCse.wordCse knowledge533 InitECandidate.Proofs.WordStages.word151_2_10604 = (knowledge534, program13820) := by
  rw [knowledge533_def, knowledge534_def]
  kernel_rfl
theorem node1067_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10605 = (knowledge534, program13821) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1065_eq node1066_eq
theorem node1068_eq : WordCse.wordCse knowledge534 InitECandidate.Proofs.WordStages.word151_2_10666 = (knowledge535, InitECandidate.Proofs.WordStages.word151_2_10666) := by
  rw [knowledge534_def, knowledge535_def]
  kernel_rfl
theorem node1069_eq : WordCse.wordCse knowledge535 InitECandidate.Proofs.WordStages.word151_2_10669 = (knowledge536, InitECandidate.Proofs.WordStages.word151_2_10669) := by
  rw [knowledge535_def, knowledge536_def]
  kernel_rfl
theorem node1070_eq : WordCse.wordCse knowledge534 InitECandidate.Proofs.WordStages.word151_2_10670 = (knowledge536, InitECandidate.Proofs.WordStages.word151_2_10670) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1068_eq node1069_eq
theorem node1071_eq : WordCse.wordCse knowledge536 InitECandidate.Proofs.WordStages.word151_2_10671 = (knowledge537, InitECandidate.Proofs.WordStages.word151_2_10671) := by
  rw [knowledge536_def, knowledge537_def]
  kernel_rfl
theorem node1072_eq : WordCse.wordCse knowledge534 InitECandidate.Proofs.WordStages.word151_2_10672 = (knowledge537, InitECandidate.Proofs.WordStages.word151_2_10672) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1070_eq node1071_eq
theorem node1073_eq : WordCse.wordCse knowledge537 InitECandidate.Proofs.WordStages.word151_2_10673 = (knowledge538, InitECandidate.Proofs.WordStages.word151_2_10673) := by
  rw [knowledge537_def, knowledge538_def]
  kernel_rfl
theorem node1074_eq : WordCse.wordCse knowledge534 InitECandidate.Proofs.WordStages.word151_2_10674 = (knowledge538, InitECandidate.Proofs.WordStages.word151_2_10674) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1072_eq node1073_eq
theorem node1075_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10675 = (knowledge538, program13822) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1067_eq node1074_eq
theorem node1076_eq : WordCse.wordCse knowledge538 InitECandidate.Proofs.WordStages.word151_2_10676 = (knowledge539, InitECandidate.Proofs.WordStages.word151_2_10676) := by
  rw [knowledge538_def, knowledge539_def]
  kernel_rfl
theorem node1077_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10677 = (knowledge539, program13823) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1075_eq node1076_eq
theorem node1078_eq : WordCse.wordCse knowledge539 InitECandidate.Proofs.WordStages.word151_2_10738 = (knowledge540, InitECandidate.Proofs.WordStages.word151_2_10738) := by
  rw [knowledge539_def, knowledge540_def]
  kernel_rfl
theorem node1079_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10739 = (knowledge540, program13824) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1077_eq node1078_eq
theorem node1080_eq : WordCse.wordCse knowledge540 InitECandidate.Proofs.WordStages.word151_2_10748 = (knowledge541, InitECandidate.Proofs.WordStages.word151_2_10748) := by
  rw [knowledge540_def, knowledge541_def]
  kernel_rfl
theorem node1081_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10749 = (knowledge541, program13825) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1079_eq node1080_eq
theorem node1082_eq : WordCse.wordCse knowledge541 InitECandidate.Proofs.WordStages.word151_2_10750 = (knowledge542, InitECandidate.Proofs.WordStages.word151_2_10750) := by
  rw [knowledge541_def, knowledge542_def]
  kernel_rfl
theorem node1083_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10751 = (knowledge542, program13826) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1081_eq node1082_eq
theorem node1084_eq : WordCse.wordCse knowledge542 InitECandidate.Proofs.WordStages.word151_2_10812 = (knowledge543, program13835) := by
  rw [knowledge542_def, knowledge543_def]
  kernel_rfl
theorem node1085_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10813 = (knowledge543, program13836) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1083_eq node1084_eq
theorem node1086_eq : WordCse.wordCse knowledge543 InitECandidate.Proofs.WordStages.word151_2_10874 = (knowledge544, InitECandidate.Proofs.WordStages.word151_2_10874) := by
  rw [knowledge543_def, knowledge544_def]
  kernel_rfl
theorem node1087_eq : WordCse.wordCse knowledge544 InitECandidate.Proofs.WordStages.word151_2_10877 = (knowledge545, InitECandidate.Proofs.WordStages.word151_2_10877) := by
  rw [knowledge544_def, knowledge545_def]
  kernel_rfl
end InitECandidate.Proofs.CseCheckpoints151
