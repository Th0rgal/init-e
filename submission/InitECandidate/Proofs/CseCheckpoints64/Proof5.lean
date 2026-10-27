import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints64.Proof4
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints64
theorem node320_eq : WordCse.wordCse knowledge160 InitECandidate.Proofs.WordStages.word64_2_922 = (knowledge161, InitECandidate.Proofs.WordStages.word64_2_922) := by
  rw [knowledge160_def, knowledge161_def]
  kernel_rfl
theorem node321_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_807 = (knowledge161, InitECandidate.Proofs.WordStages.word64_4_807) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node319_eq node320_eq
theorem node322_eq : WordCse.wordCse knowledge161 InitECandidate.Proofs.WordStages.word64_2_926 = (knowledge162, InitECandidate.Proofs.WordStages.word64_2_926) := by
  rw [knowledge161_def, knowledge162_def]
  kernel_rfl
theorem node323_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_811 = (knowledge162, InitECandidate.Proofs.WordStages.word64_4_811) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node321_eq node322_eq
theorem node324_eq : WordCse.wordCse knowledge162 InitECandidate.Proofs.WordStages.word64_2_934 = (knowledge163, InitECandidate.Proofs.WordStages.word64_4_818) := by
  rw [knowledge162_def, knowledge163_def]
  kernel_rfl
theorem node325_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_819 = (knowledge163, InitECandidate.Proofs.WordStages.word64_4_819) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node323_eq node324_eq
theorem node326_eq : WordCse.wordCse knowledge163 InitECandidate.Proofs.WordStages.word64_2_938 = (knowledge164, InitECandidate.Proofs.WordStages.word64_2_938) := by
  rw [knowledge163_def, knowledge164_def]
  kernel_rfl
theorem node327_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_821 = (knowledge164, InitECandidate.Proofs.WordStages.word64_4_821) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node325_eq node326_eq
theorem node328_eq : WordCse.wordCse knowledge164 InitECandidate.Proofs.WordStages.word64_2_942 = (knowledge165, InitECandidate.Proofs.WordStages.word64_2_942) := by
  rw [knowledge164_def, knowledge165_def]
  kernel_rfl
theorem node329_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_825 = (knowledge165, InitECandidate.Proofs.WordStages.word64_4_825) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node327_eq node328_eq
theorem node330_eq : WordCse.wordCse knowledge165 InitECandidate.Proofs.WordStages.word64_2_950 = (knowledge166, InitECandidate.Proofs.WordStages.word64_4_832) := by
  rw [knowledge165_def, knowledge166_def]
  kernel_rfl
theorem node331_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_833 = (knowledge166, InitECandidate.Proofs.WordStages.word64_4_833) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node329_eq node330_eq
theorem node332_eq : WordCse.wordCse knowledge166 InitECandidate.Proofs.WordStages.word64_2_954 = (knowledge167, InitECandidate.Proofs.WordStages.word64_2_954) := by
  rw [knowledge166_def, knowledge167_def]
  kernel_rfl
theorem node333_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_835 = (knowledge167, InitECandidate.Proofs.WordStages.word64_4_835) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node331_eq node332_eq
theorem node334_eq : WordCse.wordCse knowledge167 InitECandidate.Proofs.WordStages.word64_2_958 = (knowledge168, InitECandidate.Proofs.WordStages.word64_2_958) := by
  rw [knowledge167_def, knowledge168_def]
  kernel_rfl
theorem node335_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_839 = (knowledge168, InitECandidate.Proofs.WordStages.word64_4_839) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node333_eq node334_eq
theorem node336_eq : WordCse.wordCse knowledge168 InitECandidate.Proofs.WordStages.word64_2_966 = (knowledge169, InitECandidate.Proofs.WordStages.word64_4_846) := by
  rw [knowledge168_def, knowledge169_def]
  kernel_rfl
theorem node337_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_847 = (knowledge169, InitECandidate.Proofs.WordStages.word64_4_847) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node335_eq node336_eq
theorem node338_eq : WordCse.wordCse knowledge169 InitECandidate.Proofs.WordStages.word64_2_970 = (knowledge170, InitECandidate.Proofs.WordStages.word64_2_970) := by
  rw [knowledge169_def, knowledge170_def]
  kernel_rfl
theorem node339_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_849 = (knowledge170, InitECandidate.Proofs.WordStages.word64_4_849) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node337_eq node338_eq
theorem node340_eq : WordCse.wordCse knowledge170 InitECandidate.Proofs.WordStages.word64_2_974 = (knowledge171, InitECandidate.Proofs.WordStages.word64_2_974) := by
  rw [knowledge170_def, knowledge171_def]
  kernel_rfl
theorem node341_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_853 = (knowledge171, InitECandidate.Proofs.WordStages.word64_4_853) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node339_eq node340_eq
theorem node342_eq : WordCse.wordCse knowledge171 InitECandidate.Proofs.WordStages.word64_2_982 = (knowledge172, InitECandidate.Proofs.WordStages.word64_4_860) := by
  rw [knowledge171_def, knowledge172_def]
  kernel_rfl
theorem node343_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_861 = (knowledge172, InitECandidate.Proofs.WordStages.word64_4_861) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node341_eq node342_eq
theorem node344_eq : WordCse.wordCse knowledge172 InitECandidate.Proofs.WordStages.word64_2_986 = (knowledge173, InitECandidate.Proofs.WordStages.word64_2_986) := by
  rw [knowledge172_def, knowledge173_def]
  kernel_rfl
theorem node345_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_863 = (knowledge173, InitECandidate.Proofs.WordStages.word64_4_863) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node343_eq node344_eq
theorem node346_eq : WordCse.wordCse knowledge173 InitECandidate.Proofs.WordStages.word64_2_990 = (knowledge174, InitECandidate.Proofs.WordStages.word64_2_990) := by
  rw [knowledge173_def, knowledge174_def]
  kernel_rfl
theorem node347_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_867 = (knowledge174, InitECandidate.Proofs.WordStages.word64_4_867) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node345_eq node346_eq
theorem node348_eq : WordCse.wordCse knowledge174 InitECandidate.Proofs.WordStages.word64_2_998 = (knowledge175, InitECandidate.Proofs.WordStages.word64_4_874) := by
  rw [knowledge174_def, knowledge175_def]
  kernel_rfl
theorem node349_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_875 = (knowledge175, InitECandidate.Proofs.WordStages.word64_4_875) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node347_eq node348_eq
theorem node350_eq : WordCse.wordCse knowledge175 InitECandidate.Proofs.WordStages.word64_2_1002 = (knowledge176, InitECandidate.Proofs.WordStages.word64_2_1002) := by
  rw [knowledge175_def, knowledge176_def]
  kernel_rfl
theorem node351_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_877 = (knowledge176, InitECandidate.Proofs.WordStages.word64_4_877) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node349_eq node350_eq
theorem node352_eq : WordCse.wordCse knowledge176 InitECandidate.Proofs.WordStages.word64_2_1006 = (knowledge177, InitECandidate.Proofs.WordStages.word64_2_1006) := by
  rw [knowledge176_def, knowledge177_def]
  kernel_rfl
theorem node353_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_881 = (knowledge177, InitECandidate.Proofs.WordStages.word64_4_881) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node351_eq node352_eq
theorem node354_eq : WordCse.wordCse knowledge177 InitECandidate.Proofs.WordStages.word64_2_1014 = (knowledge178, InitECandidate.Proofs.WordStages.word64_4_888) := by
  rw [knowledge177_def, knowledge178_def]
  kernel_rfl
theorem node355_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_889 = (knowledge178, InitECandidate.Proofs.WordStages.word64_4_889) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node353_eq node354_eq
theorem node356_eq : WordCse.wordCse knowledge178 InitECandidate.Proofs.WordStages.word64_2_1018 = (knowledge179, InitECandidate.Proofs.WordStages.word64_2_1018) := by
  rw [knowledge178_def, knowledge179_def]
  kernel_rfl
theorem node357_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_891 = (knowledge179, InitECandidate.Proofs.WordStages.word64_4_891) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node355_eq node356_eq
theorem node358_eq : WordCse.wordCse knowledge179 InitECandidate.Proofs.WordStages.word64_2_1022 = (knowledge180, InitECandidate.Proofs.WordStages.word64_2_1022) := by
  rw [knowledge179_def, knowledge180_def]
  kernel_rfl
theorem node359_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_895 = (knowledge180, InitECandidate.Proofs.WordStages.word64_4_895) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node357_eq node358_eq
theorem node360_eq : WordCse.wordCse knowledge180 InitECandidate.Proofs.WordStages.word64_2_1030 = (knowledge181, InitECandidate.Proofs.WordStages.word64_4_902) := by
  rw [knowledge180_def, knowledge181_def]
  kernel_rfl
theorem node361_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_903 = (knowledge181, InitECandidate.Proofs.WordStages.word64_4_903) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node359_eq node360_eq
theorem node362_eq : WordCse.wordCse knowledge181 InitECandidate.Proofs.WordStages.word64_2_1034 = (knowledge182, InitECandidate.Proofs.WordStages.word64_2_1034) := by
  rw [knowledge181_def, knowledge182_def]
  kernel_rfl
theorem node363_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_905 = (knowledge182, InitECandidate.Proofs.WordStages.word64_4_905) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node361_eq node362_eq
theorem node364_eq : WordCse.wordCse knowledge182 InitECandidate.Proofs.WordStages.word64_2_1038 = (knowledge183, InitECandidate.Proofs.WordStages.word64_2_1038) := by
  rw [knowledge182_def, knowledge183_def]
  kernel_rfl
theorem node365_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_909 = (knowledge183, InitECandidate.Proofs.WordStages.word64_4_909) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node363_eq node364_eq
theorem node366_eq : WordCse.wordCse knowledge183 InitECandidate.Proofs.WordStages.word64_2_1046 = (knowledge184, InitECandidate.Proofs.WordStages.word64_4_916) := by
  rw [knowledge183_def, knowledge184_def]
  kernel_rfl
theorem node367_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_917 = (knowledge184, InitECandidate.Proofs.WordStages.word64_4_917) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node365_eq node366_eq
theorem node368_eq : WordCse.wordCse knowledge184 InitECandidate.Proofs.WordStages.word64_2_1050 = (knowledge185, InitECandidate.Proofs.WordStages.word64_2_1050) := by
  rw [knowledge184_def, knowledge185_def]
  kernel_rfl
theorem node369_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_919 = (knowledge185, InitECandidate.Proofs.WordStages.word64_4_919) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node367_eq node368_eq
theorem node370_eq : WordCse.wordCse knowledge185 InitECandidate.Proofs.WordStages.word64_2_1054 = (knowledge186, InitECandidate.Proofs.WordStages.word64_2_1054) := by
  rw [knowledge185_def, knowledge186_def]
  kernel_rfl
theorem node371_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_923 = (knowledge186, InitECandidate.Proofs.WordStages.word64_4_923) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node369_eq node370_eq
theorem node372_eq : WordCse.wordCse knowledge186 InitECandidate.Proofs.WordStages.word64_2_1062 = (knowledge187, InitECandidate.Proofs.WordStages.word64_4_930) := by
  rw [knowledge186_def, knowledge187_def]
  kernel_rfl
theorem node373_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_931 = (knowledge187, InitECandidate.Proofs.WordStages.word64_4_931) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node371_eq node372_eq
theorem node374_eq : WordCse.wordCse knowledge187 InitECandidate.Proofs.WordStages.word64_2_1066 = (knowledge188, InitECandidate.Proofs.WordStages.word64_2_1066) := by
  rw [knowledge187_def, knowledge188_def]
  kernel_rfl
theorem node375_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_933 = (knowledge188, InitECandidate.Proofs.WordStages.word64_4_933) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node373_eq node374_eq
theorem node376_eq : WordCse.wordCse knowledge188 InitECandidate.Proofs.WordStages.word64_2_1070 = (knowledge189, InitECandidate.Proofs.WordStages.word64_2_1070) := by
  rw [knowledge188_def, knowledge189_def]
  kernel_rfl
theorem node377_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_937 = (knowledge189, InitECandidate.Proofs.WordStages.word64_4_937) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node375_eq node376_eq
theorem node378_eq : WordCse.wordCse knowledge189 InitECandidate.Proofs.WordStages.word64_2_1074 = (knowledge0, InitECandidate.Proofs.WordStages.word64_2_1074) := by
  rw [knowledge189_def, knowledge0_def]
  kernel_rfl
theorem node379_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_941 = (knowledge0, InitECandidate.Proofs.WordStages.word64_4_941) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node377_eq node378_eq
theorem node380_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_942 = (knowledge0, InitECandidate.Proofs.WordStages.word64_4_942) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node0_eq node379_eq
end InitECandidate.Proofs.CseCheckpoints64
