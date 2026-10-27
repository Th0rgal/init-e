import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof14
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node960_eq : WordCse.wordCse knowledge480 InitECandidate.Proofs.WordStages.word151_2_9418 = (knowledge481, InitECandidate.Proofs.WordStages.word151_2_9418) := by
  rw [knowledge480_def, knowledge481_def]
  kernel_rfl
theorem node961_eq : WordCse.wordCse knowledge481 InitECandidate.Proofs.WordStages.word151_2_9421 = (knowledge482, InitECandidate.Proofs.WordStages.word151_2_9421) := by
  rw [knowledge481_def, knowledge482_def]
  kernel_rfl
theorem node962_eq : WordCse.wordCse knowledge480 InitECandidate.Proofs.WordStages.word151_2_9422 = (knowledge482, InitECandidate.Proofs.WordStages.word151_2_9422) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node960_eq node961_eq
theorem node963_eq : WordCse.wordCse knowledge482 InitECandidate.Proofs.WordStages.word151_2_9423 = (knowledge483, InitECandidate.Proofs.WordStages.word151_2_9423) := by
  rw [knowledge482_def, knowledge483_def]
  kernel_rfl
theorem node964_eq : WordCse.wordCse knowledge480 InitECandidate.Proofs.WordStages.word151_2_9424 = (knowledge483, InitECandidate.Proofs.WordStages.word151_2_9424) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node962_eq node963_eq
theorem node965_eq : WordCse.wordCse knowledge483 InitECandidate.Proofs.WordStages.word151_2_9425 = (knowledge484, InitECandidate.Proofs.WordStages.word151_2_9425) := by
  rw [knowledge483_def, knowledge484_def]
  kernel_rfl
theorem node966_eq : WordCse.wordCse knowledge480 InitECandidate.Proofs.WordStages.word151_2_9426 = (knowledge484, InitECandidate.Proofs.WordStages.word151_2_9426) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node964_eq node965_eq
theorem node967_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9427 = (knowledge484, program13732) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node959_eq node966_eq
theorem node968_eq : WordCse.wordCse knowledge484 InitECandidate.Proofs.WordStages.word151_2_9428 = (knowledge485, InitECandidate.Proofs.WordStages.word151_2_9428) := by
  rw [knowledge484_def, knowledge485_def]
  kernel_rfl
theorem node969_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9429 = (knowledge485, program13733) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node967_eq node968_eq
theorem node970_eq : WordCse.wordCse knowledge485 InitECandidate.Proofs.WordStages.word151_2_9490 = (knowledge486, InitECandidate.Proofs.WordStages.word151_2_9490) := by
  rw [knowledge485_def, knowledge486_def]
  kernel_rfl
theorem node971_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9491 = (knowledge486, program13734) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node969_eq node970_eq
theorem node972_eq : WordCse.wordCse knowledge486 InitECandidate.Proofs.WordStages.word151_2_9500 = (knowledge487, InitECandidate.Proofs.WordStages.word151_2_9500) := by
  rw [knowledge486_def, knowledge487_def]
  kernel_rfl
theorem node973_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9501 = (knowledge487, program13735) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node971_eq node972_eq
theorem node974_eq : WordCse.wordCse knowledge487 InitECandidate.Proofs.WordStages.word151_2_9502 = (knowledge488, InitECandidate.Proofs.WordStages.word151_2_9502) := by
  rw [knowledge487_def, knowledge488_def]
  kernel_rfl
theorem node975_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9503 = (knowledge488, program13736) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node973_eq node974_eq
theorem node976_eq : WordCse.wordCse knowledge488 InitECandidate.Proofs.WordStages.word151_2_9564 = (knowledge489, program13745) := by
  rw [knowledge488_def, knowledge489_def]
  kernel_rfl
theorem node977_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9565 = (knowledge489, program13746) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node975_eq node976_eq
theorem node978_eq : WordCse.wordCse knowledge489 InitECandidate.Proofs.WordStages.word151_2_9626 = (knowledge490, InitECandidate.Proofs.WordStages.word151_2_9626) := by
  rw [knowledge489_def, knowledge490_def]
  kernel_rfl
theorem node979_eq : WordCse.wordCse knowledge490 InitECandidate.Proofs.WordStages.word151_2_9629 = (knowledge491, InitECandidate.Proofs.WordStages.word151_2_9629) := by
  rw [knowledge490_def, knowledge491_def]
  kernel_rfl
theorem node980_eq : WordCse.wordCse knowledge489 InitECandidate.Proofs.WordStages.word151_2_9630 = (knowledge491, InitECandidate.Proofs.WordStages.word151_2_9630) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node978_eq node979_eq
theorem node981_eq : WordCse.wordCse knowledge491 InitECandidate.Proofs.WordStages.word151_2_9631 = (knowledge492, InitECandidate.Proofs.WordStages.word151_2_9631) := by
  rw [knowledge491_def, knowledge492_def]
  kernel_rfl
theorem node982_eq : WordCse.wordCse knowledge489 InitECandidate.Proofs.WordStages.word151_2_9632 = (knowledge492, InitECandidate.Proofs.WordStages.word151_2_9632) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node980_eq node981_eq
theorem node983_eq : WordCse.wordCse knowledge492 InitECandidate.Proofs.WordStages.word151_2_9633 = (knowledge493, InitECandidate.Proofs.WordStages.word151_2_9633) := by
  rw [knowledge492_def, knowledge493_def]
  kernel_rfl
theorem node984_eq : WordCse.wordCse knowledge489 InitECandidate.Proofs.WordStages.word151_2_9634 = (knowledge493, InitECandidate.Proofs.WordStages.word151_2_9634) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node982_eq node983_eq
theorem node985_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9635 = (knowledge493, program13747) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node977_eq node984_eq
theorem node986_eq : WordCse.wordCse knowledge493 InitECandidate.Proofs.WordStages.word151_2_9636 = (knowledge494, InitECandidate.Proofs.WordStages.word151_2_9636) := by
  rw [knowledge493_def, knowledge494_def]
  kernel_rfl
theorem node987_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9637 = (knowledge494, program13748) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node985_eq node986_eq
theorem node988_eq : WordCse.wordCse knowledge494 InitECandidate.Proofs.WordStages.word151_2_9698 = (knowledge495, InitECandidate.Proofs.WordStages.word151_2_9698) := by
  rw [knowledge494_def, knowledge495_def]
  kernel_rfl
theorem node989_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9699 = (knowledge495, program13749) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node987_eq node988_eq
theorem node990_eq : WordCse.wordCse knowledge495 InitECandidate.Proofs.WordStages.word151_2_9708 = (knowledge496, InitECandidate.Proofs.WordStages.word151_2_9708) := by
  rw [knowledge495_def, knowledge496_def]
  kernel_rfl
theorem node991_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9709 = (knowledge496, program13750) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node989_eq node990_eq
theorem node992_eq : WordCse.wordCse knowledge496 InitECandidate.Proofs.WordStages.word151_2_9710 = (knowledge497, InitECandidate.Proofs.WordStages.word151_2_9710) := by
  rw [knowledge496_def, knowledge497_def]
  kernel_rfl
theorem node993_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9711 = (knowledge497, program13751) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node991_eq node992_eq
theorem node994_eq : WordCse.wordCse knowledge497 InitECandidate.Proofs.WordStages.word151_2_9772 = (knowledge498, program13760) := by
  rw [knowledge497_def, knowledge498_def]
  kernel_rfl
theorem node995_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9773 = (knowledge498, program13761) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node993_eq node994_eq
theorem node996_eq : WordCse.wordCse knowledge498 InitECandidate.Proofs.WordStages.word151_2_9834 = (knowledge499, InitECandidate.Proofs.WordStages.word151_2_9834) := by
  rw [knowledge498_def, knowledge499_def]
  kernel_rfl
theorem node997_eq : WordCse.wordCse knowledge499 InitECandidate.Proofs.WordStages.word151_2_9837 = (knowledge500, InitECandidate.Proofs.WordStages.word151_2_9837) := by
  rw [knowledge499_def, knowledge500_def]
  kernel_rfl
theorem node998_eq : WordCse.wordCse knowledge498 InitECandidate.Proofs.WordStages.word151_2_9838 = (knowledge500, InitECandidate.Proofs.WordStages.word151_2_9838) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node996_eq node997_eq
theorem node999_eq : WordCse.wordCse knowledge500 InitECandidate.Proofs.WordStages.word151_2_9839 = (knowledge501, InitECandidate.Proofs.WordStages.word151_2_9839) := by
  rw [knowledge500_def, knowledge501_def]
  kernel_rfl
theorem node1000_eq : WordCse.wordCse knowledge498 InitECandidate.Proofs.WordStages.word151_2_9840 = (knowledge501, InitECandidate.Proofs.WordStages.word151_2_9840) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node998_eq node999_eq
theorem node1001_eq : WordCse.wordCse knowledge501 InitECandidate.Proofs.WordStages.word151_2_9841 = (knowledge502, InitECandidate.Proofs.WordStages.word151_2_9841) := by
  rw [knowledge501_def, knowledge502_def]
  kernel_rfl
theorem node1002_eq : WordCse.wordCse knowledge498 InitECandidate.Proofs.WordStages.word151_2_9842 = (knowledge502, InitECandidate.Proofs.WordStages.word151_2_9842) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1000_eq node1001_eq
theorem node1003_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9843 = (knowledge502, program13762) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node995_eq node1002_eq
theorem node1004_eq : WordCse.wordCse knowledge502 InitECandidate.Proofs.WordStages.word151_2_9844 = (knowledge503, InitECandidate.Proofs.WordStages.word151_2_9844) := by
  rw [knowledge502_def, knowledge503_def]
  kernel_rfl
theorem node1005_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9845 = (knowledge503, program13763) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1003_eq node1004_eq
theorem node1006_eq : WordCse.wordCse knowledge503 InitECandidate.Proofs.WordStages.word151_2_9906 = (knowledge504, InitECandidate.Proofs.WordStages.word151_2_9906) := by
  rw [knowledge503_def, knowledge504_def]
  kernel_rfl
theorem node1007_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9907 = (knowledge504, program13764) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1005_eq node1006_eq
theorem node1008_eq : WordCse.wordCse knowledge504 InitECandidate.Proofs.WordStages.word151_2_9916 = (knowledge505, InitECandidate.Proofs.WordStages.word151_2_9916) := by
  rw [knowledge504_def, knowledge505_def]
  kernel_rfl
theorem node1009_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9917 = (knowledge505, program13765) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1007_eq node1008_eq
theorem node1010_eq : WordCse.wordCse knowledge505 InitECandidate.Proofs.WordStages.word151_2_9918 = (knowledge506, InitECandidate.Proofs.WordStages.word151_2_9918) := by
  rw [knowledge505_def, knowledge506_def]
  kernel_rfl
theorem node1011_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9919 = (knowledge506, program13766) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1009_eq node1010_eq
theorem node1012_eq : WordCse.wordCse knowledge506 InitECandidate.Proofs.WordStages.word151_2_9980 = (knowledge507, program13775) := by
  rw [knowledge506_def, knowledge507_def]
  kernel_rfl
theorem node1013_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_9981 = (knowledge507, program13776) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1011_eq node1012_eq
theorem node1014_eq : WordCse.wordCse knowledge507 InitECandidate.Proofs.WordStages.word151_2_10042 = (knowledge508, InitECandidate.Proofs.WordStages.word151_2_10042) := by
  rw [knowledge507_def, knowledge508_def]
  kernel_rfl
theorem node1015_eq : WordCse.wordCse knowledge508 InitECandidate.Proofs.WordStages.word151_2_10045 = (knowledge509, InitECandidate.Proofs.WordStages.word151_2_10045) := by
  rw [knowledge508_def, knowledge509_def]
  kernel_rfl
theorem node1016_eq : WordCse.wordCse knowledge507 InitECandidate.Proofs.WordStages.word151_2_10046 = (knowledge509, InitECandidate.Proofs.WordStages.word151_2_10046) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1014_eq node1015_eq
theorem node1017_eq : WordCse.wordCse knowledge509 InitECandidate.Proofs.WordStages.word151_2_10047 = (knowledge510, InitECandidate.Proofs.WordStages.word151_2_10047) := by
  rw [knowledge509_def, knowledge510_def]
  kernel_rfl
theorem node1018_eq : WordCse.wordCse knowledge507 InitECandidate.Proofs.WordStages.word151_2_10048 = (knowledge510, InitECandidate.Proofs.WordStages.word151_2_10048) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1016_eq node1017_eq
theorem node1019_eq : WordCse.wordCse knowledge510 InitECandidate.Proofs.WordStages.word151_2_10049 = (knowledge511, InitECandidate.Proofs.WordStages.word151_2_10049) := by
  rw [knowledge510_def, knowledge511_def]
  kernel_rfl
theorem node1020_eq : WordCse.wordCse knowledge507 InitECandidate.Proofs.WordStages.word151_2_10050 = (knowledge511, InitECandidate.Proofs.WordStages.word151_2_10050) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1018_eq node1019_eq
theorem node1021_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10051 = (knowledge511, program13777) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1013_eq node1020_eq
theorem node1022_eq : WordCse.wordCse knowledge511 InitECandidate.Proofs.WordStages.word151_2_10052 = (knowledge512, InitECandidate.Proofs.WordStages.word151_2_10052) := by
  rw [knowledge511_def, knowledge512_def]
  kernel_rfl
theorem node1023_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_10053 = (knowledge512, program13778) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node1021_eq node1022_eq
end InitECandidate.Proofs.CseCheckpoints151
