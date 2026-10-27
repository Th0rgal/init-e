import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints64.Proof3
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints64
theorem node256_eq : WordCse.wordCse knowledge128 InitECandidate.Proofs.WordStages.word64_2_750 = (knowledge129, InitECandidate.Proofs.WordStages.word64_2_750) := by
  rw [knowledge128_def, knowledge129_def]
  kernel_rfl
theorem node257_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_657 = (knowledge129, InitECandidate.Proofs.WordStages.word64_4_657) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node255_eq node256_eq
theorem node258_eq : WordCse.wordCse knowledge129 InitECandidate.Proofs.WordStages.word64_2_758 = (knowledge130, InitECandidate.Proofs.WordStages.word64_4_664) := by
  rw [knowledge129_def, knowledge130_def]
  kernel_rfl
theorem node259_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_665 = (knowledge130, InitECandidate.Proofs.WordStages.word64_4_665) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node257_eq node258_eq
theorem node260_eq : WordCse.wordCse knowledge130 InitECandidate.Proofs.WordStages.word64_2_762 = (knowledge131, InitECandidate.Proofs.WordStages.word64_2_762) := by
  rw [knowledge130_def, knowledge131_def]
  kernel_rfl
theorem node261_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_667 = (knowledge131, InitECandidate.Proofs.WordStages.word64_4_667) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node259_eq node260_eq
theorem node262_eq : WordCse.wordCse knowledge131 InitECandidate.Proofs.WordStages.word64_2_766 = (knowledge132, InitECandidate.Proofs.WordStages.word64_2_766) := by
  rw [knowledge131_def, knowledge132_def]
  kernel_rfl
theorem node263_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_671 = (knowledge132, InitECandidate.Proofs.WordStages.word64_4_671) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node261_eq node262_eq
theorem node264_eq : WordCse.wordCse knowledge132 InitECandidate.Proofs.WordStages.word64_2_774 = (knowledge133, InitECandidate.Proofs.WordStages.word64_4_678) := by
  rw [knowledge132_def, knowledge133_def]
  kernel_rfl
theorem node265_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_679 = (knowledge133, InitECandidate.Proofs.WordStages.word64_4_679) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node263_eq node264_eq
theorem node266_eq : WordCse.wordCse knowledge133 InitECandidate.Proofs.WordStages.word64_2_778 = (knowledge134, InitECandidate.Proofs.WordStages.word64_2_778) := by
  rw [knowledge133_def, knowledge134_def]
  kernel_rfl
theorem node267_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_681 = (knowledge134, InitECandidate.Proofs.WordStages.word64_4_681) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node265_eq node266_eq
theorem node268_eq : WordCse.wordCse knowledge134 InitECandidate.Proofs.WordStages.word64_2_782 = (knowledge135, InitECandidate.Proofs.WordStages.word64_2_782) := by
  rw [knowledge134_def, knowledge135_def]
  kernel_rfl
theorem node269_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_685 = (knowledge135, InitECandidate.Proofs.WordStages.word64_4_685) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node267_eq node268_eq
theorem node270_eq : WordCse.wordCse knowledge135 InitECandidate.Proofs.WordStages.word64_2_790 = (knowledge136, InitECandidate.Proofs.WordStages.word64_4_692) := by
  rw [knowledge135_def, knowledge136_def]
  kernel_rfl
theorem node271_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_693 = (knowledge136, InitECandidate.Proofs.WordStages.word64_4_693) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node269_eq node270_eq
theorem node272_eq : WordCse.wordCse knowledge136 InitECandidate.Proofs.WordStages.word64_2_794 = (knowledge137, InitECandidate.Proofs.WordStages.word64_2_794) := by
  rw [knowledge136_def, knowledge137_def]
  kernel_rfl
theorem node273_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_695 = (knowledge137, InitECandidate.Proofs.WordStages.word64_4_695) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node271_eq node272_eq
theorem node274_eq : WordCse.wordCse knowledge137 InitECandidate.Proofs.WordStages.word64_2_798 = (knowledge138, InitECandidate.Proofs.WordStages.word64_2_798) := by
  rw [knowledge137_def, knowledge138_def]
  kernel_rfl
theorem node275_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_699 = (knowledge138, InitECandidate.Proofs.WordStages.word64_4_699) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node273_eq node274_eq
theorem node276_eq : WordCse.wordCse knowledge138 InitECandidate.Proofs.WordStages.word64_2_806 = (knowledge139, InitECandidate.Proofs.WordStages.word64_4_706) := by
  rw [knowledge138_def, knowledge139_def]
  kernel_rfl
theorem node277_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_707 = (knowledge139, InitECandidate.Proofs.WordStages.word64_4_707) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node275_eq node276_eq
theorem node278_eq : WordCse.wordCse knowledge139 InitECandidate.Proofs.WordStages.word64_2_810 = (knowledge140, InitECandidate.Proofs.WordStages.word64_2_810) := by
  rw [knowledge139_def, knowledge140_def]
  kernel_rfl
theorem node279_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_709 = (knowledge140, InitECandidate.Proofs.WordStages.word64_4_709) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node277_eq node278_eq
theorem node280_eq : WordCse.wordCse knowledge140 InitECandidate.Proofs.WordStages.word64_2_814 = (knowledge141, InitECandidate.Proofs.WordStages.word64_2_814) := by
  rw [knowledge140_def, knowledge141_def]
  kernel_rfl
theorem node281_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_713 = (knowledge141, InitECandidate.Proofs.WordStages.word64_4_713) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node279_eq node280_eq
theorem node282_eq : WordCse.wordCse knowledge141 InitECandidate.Proofs.WordStages.word64_2_822 = (knowledge142, InitECandidate.Proofs.WordStages.word64_4_720) := by
  rw [knowledge141_def, knowledge142_def]
  kernel_rfl
theorem node283_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_721 = (knowledge142, InitECandidate.Proofs.WordStages.word64_4_721) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node281_eq node282_eq
theorem node284_eq : WordCse.wordCse knowledge142 InitECandidate.Proofs.WordStages.word64_2_826 = (knowledge143, InitECandidate.Proofs.WordStages.word64_2_826) := by
  rw [knowledge142_def, knowledge143_def]
  kernel_rfl
theorem node285_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_723 = (knowledge143, InitECandidate.Proofs.WordStages.word64_4_723) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node283_eq node284_eq
theorem node286_eq : WordCse.wordCse knowledge143 InitECandidate.Proofs.WordStages.word64_2_830 = (knowledge144, InitECandidate.Proofs.WordStages.word64_2_830) := by
  rw [knowledge143_def, knowledge144_def]
  kernel_rfl
theorem node287_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_727 = (knowledge144, InitECandidate.Proofs.WordStages.word64_4_727) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node285_eq node286_eq
theorem node288_eq : WordCse.wordCse knowledge144 InitECandidate.Proofs.WordStages.word64_2_838 = (knowledge145, InitECandidate.Proofs.WordStages.word64_4_734) := by
  rw [knowledge144_def, knowledge145_def]
  kernel_rfl
theorem node289_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_735 = (knowledge145, InitECandidate.Proofs.WordStages.word64_4_735) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node287_eq node288_eq
theorem node290_eq : WordCse.wordCse knowledge145 InitECandidate.Proofs.WordStages.word64_2_842 = (knowledge146, InitECandidate.Proofs.WordStages.word64_2_842) := by
  rw [knowledge145_def, knowledge146_def]
  kernel_rfl
theorem node291_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_737 = (knowledge146, InitECandidate.Proofs.WordStages.word64_4_737) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node289_eq node290_eq
theorem node292_eq : WordCse.wordCse knowledge146 InitECandidate.Proofs.WordStages.word64_2_846 = (knowledge147, InitECandidate.Proofs.WordStages.word64_2_846) := by
  rw [knowledge146_def, knowledge147_def]
  kernel_rfl
theorem node293_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_741 = (knowledge147, InitECandidate.Proofs.WordStages.word64_4_741) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node291_eq node292_eq
theorem node294_eq : WordCse.wordCse knowledge147 InitECandidate.Proofs.WordStages.word64_2_854 = (knowledge148, InitECandidate.Proofs.WordStages.word64_4_748) := by
  rw [knowledge147_def, knowledge148_def]
  kernel_rfl
theorem node295_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_749 = (knowledge148, InitECandidate.Proofs.WordStages.word64_4_749) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node293_eq node294_eq
theorem node296_eq : WordCse.wordCse knowledge148 InitECandidate.Proofs.WordStages.word64_2_858 = (knowledge149, InitECandidate.Proofs.WordStages.word64_2_858) := by
  rw [knowledge148_def, knowledge149_def]
  kernel_rfl
theorem node297_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_751 = (knowledge149, InitECandidate.Proofs.WordStages.word64_4_751) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node295_eq node296_eq
theorem node298_eq : WordCse.wordCse knowledge149 InitECandidate.Proofs.WordStages.word64_2_862 = (knowledge150, InitECandidate.Proofs.WordStages.word64_2_862) := by
  rw [knowledge149_def, knowledge150_def]
  kernel_rfl
theorem node299_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_755 = (knowledge150, InitECandidate.Proofs.WordStages.word64_4_755) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node297_eq node298_eq
theorem node300_eq : WordCse.wordCse knowledge150 InitECandidate.Proofs.WordStages.word64_2_870 = (knowledge151, InitECandidate.Proofs.WordStages.word64_4_762) := by
  rw [knowledge150_def, knowledge151_def]
  kernel_rfl
theorem node301_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_763 = (knowledge151, InitECandidate.Proofs.WordStages.word64_4_763) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node299_eq node300_eq
theorem node302_eq : WordCse.wordCse knowledge151 InitECandidate.Proofs.WordStages.word64_2_874 = (knowledge152, InitECandidate.Proofs.WordStages.word64_2_874) := by
  rw [knowledge151_def, knowledge152_def]
  kernel_rfl
theorem node303_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_765 = (knowledge152, InitECandidate.Proofs.WordStages.word64_4_765) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node301_eq node302_eq
theorem node304_eq : WordCse.wordCse knowledge152 InitECandidate.Proofs.WordStages.word64_2_878 = (knowledge153, InitECandidate.Proofs.WordStages.word64_2_878) := by
  rw [knowledge152_def, knowledge153_def]
  kernel_rfl
theorem node305_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_769 = (knowledge153, InitECandidate.Proofs.WordStages.word64_4_769) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node303_eq node304_eq
theorem node306_eq : WordCse.wordCse knowledge153 InitECandidate.Proofs.WordStages.word64_2_886 = (knowledge154, InitECandidate.Proofs.WordStages.word64_4_776) := by
  rw [knowledge153_def, knowledge154_def]
  kernel_rfl
theorem node307_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_777 = (knowledge154, InitECandidate.Proofs.WordStages.word64_4_777) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node305_eq node306_eq
theorem node308_eq : WordCse.wordCse knowledge154 InitECandidate.Proofs.WordStages.word64_2_890 = (knowledge155, InitECandidate.Proofs.WordStages.word64_2_890) := by
  rw [knowledge154_def, knowledge155_def]
  kernel_rfl
theorem node309_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_779 = (knowledge155, InitECandidate.Proofs.WordStages.word64_4_779) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node307_eq node308_eq
theorem node310_eq : WordCse.wordCse knowledge155 InitECandidate.Proofs.WordStages.word64_2_894 = (knowledge156, InitECandidate.Proofs.WordStages.word64_2_894) := by
  rw [knowledge155_def, knowledge156_def]
  kernel_rfl
theorem node311_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_783 = (knowledge156, InitECandidate.Proofs.WordStages.word64_4_783) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node309_eq node310_eq
theorem node312_eq : WordCse.wordCse knowledge156 InitECandidate.Proofs.WordStages.word64_2_902 = (knowledge157, InitECandidate.Proofs.WordStages.word64_4_790) := by
  rw [knowledge156_def, knowledge157_def]
  kernel_rfl
theorem node313_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_791 = (knowledge157, InitECandidate.Proofs.WordStages.word64_4_791) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node311_eq node312_eq
theorem node314_eq : WordCse.wordCse knowledge157 InitECandidate.Proofs.WordStages.word64_2_906 = (knowledge158, InitECandidate.Proofs.WordStages.word64_2_906) := by
  rw [knowledge157_def, knowledge158_def]
  kernel_rfl
theorem node315_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_793 = (knowledge158, InitECandidate.Proofs.WordStages.word64_4_793) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node313_eq node314_eq
theorem node316_eq : WordCse.wordCse knowledge158 InitECandidate.Proofs.WordStages.word64_2_910 = (knowledge159, InitECandidate.Proofs.WordStages.word64_2_910) := by
  rw [knowledge158_def, knowledge159_def]
  kernel_rfl
theorem node317_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_797 = (knowledge159, InitECandidate.Proofs.WordStages.word64_4_797) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node315_eq node316_eq
theorem node318_eq : WordCse.wordCse knowledge159 InitECandidate.Proofs.WordStages.word64_2_918 = (knowledge160, InitECandidate.Proofs.WordStages.word64_4_804) := by
  rw [knowledge159_def, knowledge160_def]
  kernel_rfl
theorem node319_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_805 = (knowledge160, InitECandidate.Proofs.WordStages.word64_4_805) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node317_eq node318_eq
end InitECandidate.Proofs.CseCheckpoints64
