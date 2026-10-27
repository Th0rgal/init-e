import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof6
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node448_eq : WordCse.wordCse knowledge224 InitECandidate.Proofs.WordStages.word151_2_3458 = (knowledge225, InitECandidate.Proofs.WordStages.word151_2_3458) := by
  rw [knowledge224_def, knowledge225_def]
  kernel_rfl
theorem node449_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3459 = (knowledge225, program13299) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node447_eq node448_eq
theorem node450_eq : WordCse.wordCse knowledge225 InitECandidate.Proofs.WordStages.word151_2_3468 = (knowledge226, InitECandidate.Proofs.WordStages.word151_2_3468) := by
  rw [knowledge225_def, knowledge226_def]
  kernel_rfl
theorem node451_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3469 = (knowledge226, program13300) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node449_eq node450_eq
theorem node452_eq : WordCse.wordCse knowledge226 InitECandidate.Proofs.WordStages.word151_2_3470 = (knowledge227, InitECandidate.Proofs.WordStages.word151_2_3470) := by
  rw [knowledge226_def, knowledge227_def]
  kernel_rfl
theorem node453_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3471 = (knowledge227, program13301) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node451_eq node452_eq
theorem node454_eq : WordCse.wordCse knowledge227 InitECandidate.Proofs.WordStages.word151_2_3532 = (knowledge228, program13310) := by
  rw [knowledge227_def, knowledge228_def]
  kernel_rfl
theorem node455_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3533 = (knowledge228, program13311) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node453_eq node454_eq
theorem node456_eq : WordCse.wordCse knowledge228 InitECandidate.Proofs.WordStages.word151_2_3594 = (knowledge229, InitECandidate.Proofs.WordStages.word151_2_3594) := by
  rw [knowledge228_def, knowledge229_def]
  kernel_rfl
theorem node457_eq : WordCse.wordCse knowledge229 InitECandidate.Proofs.WordStages.word151_2_3597 = (knowledge230, InitECandidate.Proofs.WordStages.word151_2_3597) := by
  rw [knowledge229_def, knowledge230_def]
  kernel_rfl
theorem node458_eq : WordCse.wordCse knowledge228 InitECandidate.Proofs.WordStages.word151_2_3598 = (knowledge230, InitECandidate.Proofs.WordStages.word151_2_3598) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node456_eq node457_eq
theorem node459_eq : WordCse.wordCse knowledge230 InitECandidate.Proofs.WordStages.word151_2_3599 = (knowledge231, InitECandidate.Proofs.WordStages.word151_2_3599) := by
  rw [knowledge230_def, knowledge231_def]
  kernel_rfl
theorem node460_eq : WordCse.wordCse knowledge228 InitECandidate.Proofs.WordStages.word151_2_3600 = (knowledge231, InitECandidate.Proofs.WordStages.word151_2_3600) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node458_eq node459_eq
theorem node461_eq : WordCse.wordCse knowledge231 InitECandidate.Proofs.WordStages.word151_2_3601 = (knowledge232, InitECandidate.Proofs.WordStages.word151_2_3601) := by
  rw [knowledge231_def, knowledge232_def]
  kernel_rfl
theorem node462_eq : WordCse.wordCse knowledge228 InitECandidate.Proofs.WordStages.word151_2_3602 = (knowledge232, InitECandidate.Proofs.WordStages.word151_2_3602) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node460_eq node461_eq
theorem node463_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3603 = (knowledge232, program13312) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node455_eq node462_eq
theorem node464_eq : WordCse.wordCse knowledge232 InitECandidate.Proofs.WordStages.word151_2_3604 = (knowledge233, InitECandidate.Proofs.WordStages.word151_2_3604) := by
  rw [knowledge232_def, knowledge233_def]
  kernel_rfl
theorem node465_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3605 = (knowledge233, program13313) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node463_eq node464_eq
theorem node466_eq : WordCse.wordCse knowledge233 InitECandidate.Proofs.WordStages.word151_2_3666 = (knowledge234, InitECandidate.Proofs.WordStages.word151_2_3666) := by
  rw [knowledge233_def, knowledge234_def]
  kernel_rfl
theorem node467_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3667 = (knowledge234, program13314) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node465_eq node466_eq
theorem node468_eq : WordCse.wordCse knowledge234 InitECandidate.Proofs.WordStages.word151_2_3676 = (knowledge235, InitECandidate.Proofs.WordStages.word151_2_3676) := by
  rw [knowledge234_def, knowledge235_def]
  kernel_rfl
theorem node469_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3677 = (knowledge235, program13315) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node467_eq node468_eq
theorem node470_eq : WordCse.wordCse knowledge235 InitECandidate.Proofs.WordStages.word151_2_3678 = (knowledge236, InitECandidate.Proofs.WordStages.word151_2_3678) := by
  rw [knowledge235_def, knowledge236_def]
  kernel_rfl
theorem node471_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3679 = (knowledge236, program13316) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node469_eq node470_eq
theorem node472_eq : WordCse.wordCse knowledge236 InitECandidate.Proofs.WordStages.word151_2_3740 = (knowledge237, program13325) := by
  rw [knowledge236_def, knowledge237_def]
  kernel_rfl
theorem node473_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3741 = (knowledge237, program13326) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node471_eq node472_eq
theorem node474_eq : WordCse.wordCse knowledge237 InitECandidate.Proofs.WordStages.word151_2_3802 = (knowledge238, InitECandidate.Proofs.WordStages.word151_2_3802) := by
  rw [knowledge237_def, knowledge238_def]
  kernel_rfl
theorem node475_eq : WordCse.wordCse knowledge238 InitECandidate.Proofs.WordStages.word151_2_3805 = (knowledge239, InitECandidate.Proofs.WordStages.word151_2_3805) := by
  rw [knowledge238_def, knowledge239_def]
  kernel_rfl
theorem node476_eq : WordCse.wordCse knowledge237 InitECandidate.Proofs.WordStages.word151_2_3806 = (knowledge239, InitECandidate.Proofs.WordStages.word151_2_3806) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node474_eq node475_eq
theorem node477_eq : WordCse.wordCse knowledge239 InitECandidate.Proofs.WordStages.word151_2_3807 = (knowledge240, InitECandidate.Proofs.WordStages.word151_2_3807) := by
  rw [knowledge239_def, knowledge240_def]
  kernel_rfl
theorem node478_eq : WordCse.wordCse knowledge237 InitECandidate.Proofs.WordStages.word151_2_3808 = (knowledge240, InitECandidate.Proofs.WordStages.word151_2_3808) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node476_eq node477_eq
theorem node479_eq : WordCse.wordCse knowledge240 InitECandidate.Proofs.WordStages.word151_2_3809 = (knowledge241, InitECandidate.Proofs.WordStages.word151_2_3809) := by
  rw [knowledge240_def, knowledge241_def]
  kernel_rfl
theorem node480_eq : WordCse.wordCse knowledge237 InitECandidate.Proofs.WordStages.word151_2_3810 = (knowledge241, InitECandidate.Proofs.WordStages.word151_2_3810) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node478_eq node479_eq
theorem node481_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3811 = (knowledge241, program13327) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node473_eq node480_eq
theorem node482_eq : WordCse.wordCse knowledge241 InitECandidate.Proofs.WordStages.word151_2_3812 = (knowledge242, InitECandidate.Proofs.WordStages.word151_2_3812) := by
  rw [knowledge241_def, knowledge242_def]
  kernel_rfl
theorem node483_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3813 = (knowledge242, program13328) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node481_eq node482_eq
theorem node484_eq : WordCse.wordCse knowledge242 InitECandidate.Proofs.WordStages.word151_2_3874 = (knowledge243, InitECandidate.Proofs.WordStages.word151_2_3874) := by
  rw [knowledge242_def, knowledge243_def]
  kernel_rfl
theorem node485_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3875 = (knowledge243, program13329) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node483_eq node484_eq
theorem node486_eq : WordCse.wordCse knowledge243 InitECandidate.Proofs.WordStages.word151_2_3884 = (knowledge244, InitECandidate.Proofs.WordStages.word151_2_3884) := by
  rw [knowledge243_def, knowledge244_def]
  kernel_rfl
theorem node487_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3885 = (knowledge244, program13330) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node485_eq node486_eq
theorem node488_eq : WordCse.wordCse knowledge244 InitECandidate.Proofs.WordStages.word151_2_3886 = (knowledge245, InitECandidate.Proofs.WordStages.word151_2_3886) := by
  rw [knowledge244_def, knowledge245_def]
  kernel_rfl
theorem node489_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3887 = (knowledge245, program13331) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node487_eq node488_eq
theorem node490_eq : WordCse.wordCse knowledge245 InitECandidate.Proofs.WordStages.word151_2_3948 = (knowledge246, program13340) := by
  rw [knowledge245_def, knowledge246_def]
  kernel_rfl
theorem node491_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_3949 = (knowledge246, program13341) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node489_eq node490_eq
theorem node492_eq : WordCse.wordCse knowledge246 InitECandidate.Proofs.WordStages.word151_2_4010 = (knowledge247, InitECandidate.Proofs.WordStages.word151_2_4010) := by
  rw [knowledge246_def, knowledge247_def]
  kernel_rfl
theorem node493_eq : WordCse.wordCse knowledge247 InitECandidate.Proofs.WordStages.word151_2_4013 = (knowledge248, InitECandidate.Proofs.WordStages.word151_2_4013) := by
  rw [knowledge247_def, knowledge248_def]
  kernel_rfl
theorem node494_eq : WordCse.wordCse knowledge246 InitECandidate.Proofs.WordStages.word151_2_4014 = (knowledge248, InitECandidate.Proofs.WordStages.word151_2_4014) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node492_eq node493_eq
theorem node495_eq : WordCse.wordCse knowledge248 InitECandidate.Proofs.WordStages.word151_2_4015 = (knowledge249, InitECandidate.Proofs.WordStages.word151_2_4015) := by
  rw [knowledge248_def, knowledge249_def]
  kernel_rfl
theorem node496_eq : WordCse.wordCse knowledge246 InitECandidate.Proofs.WordStages.word151_2_4016 = (knowledge249, InitECandidate.Proofs.WordStages.word151_2_4016) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node494_eq node495_eq
theorem node497_eq : WordCse.wordCse knowledge249 InitECandidate.Proofs.WordStages.word151_2_4017 = (knowledge250, InitECandidate.Proofs.WordStages.word151_2_4017) := by
  rw [knowledge249_def, knowledge250_def]
  kernel_rfl
theorem node498_eq : WordCse.wordCse knowledge246 InitECandidate.Proofs.WordStages.word151_2_4018 = (knowledge250, InitECandidate.Proofs.WordStages.word151_2_4018) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node496_eq node497_eq
theorem node499_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_4019 = (knowledge250, program13342) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node491_eq node498_eq
theorem node500_eq : WordCse.wordCse knowledge250 InitECandidate.Proofs.WordStages.word151_2_4020 = (knowledge251, InitECandidate.Proofs.WordStages.word151_2_4020) := by
  rw [knowledge250_def, knowledge251_def]
  kernel_rfl
theorem node501_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_4021 = (knowledge251, program13343) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node499_eq node500_eq
theorem node502_eq : WordCse.wordCse knowledge251 InitECandidate.Proofs.WordStages.word151_2_4082 = (knowledge252, InitECandidate.Proofs.WordStages.word151_2_4082) := by
  rw [knowledge251_def, knowledge252_def]
  kernel_rfl
theorem node503_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_4083 = (knowledge252, program13344) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node501_eq node502_eq
theorem node504_eq : WordCse.wordCse knowledge252 InitECandidate.Proofs.WordStages.word151_2_4092 = (knowledge253, InitECandidate.Proofs.WordStages.word151_2_4092) := by
  rw [knowledge252_def, knowledge253_def]
  kernel_rfl
theorem node505_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_4093 = (knowledge253, program13345) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node503_eq node504_eq
theorem node506_eq : WordCse.wordCse knowledge253 InitECandidate.Proofs.WordStages.word151_2_4094 = (knowledge254, InitECandidate.Proofs.WordStages.word151_2_4094) := by
  rw [knowledge253_def, knowledge254_def]
  kernel_rfl
theorem node507_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_4095 = (knowledge254, program13346) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node505_eq node506_eq
theorem node508_eq : WordCse.wordCse knowledge254 InitECandidate.Proofs.WordStages.word151_2_4156 = (knowledge255, program13355) := by
  rw [knowledge254_def, knowledge255_def]
  kernel_rfl
theorem node509_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_4157 = (knowledge255, program13356) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node507_eq node508_eq
theorem node510_eq : WordCse.wordCse knowledge255 InitECandidate.Proofs.WordStages.word151_2_4218 = (knowledge256, InitECandidate.Proofs.WordStages.word151_2_4218) := by
  rw [knowledge255_def, knowledge256_def]
  kernel_rfl
theorem node511_eq : WordCse.wordCse knowledge256 InitECandidate.Proofs.WordStages.word151_2_4221 = (knowledge257, InitECandidate.Proofs.WordStages.word151_2_4221) := by
  rw [knowledge256_def, knowledge257_def]
  kernel_rfl
end InitECandidate.Proofs.CseCheckpoints151
