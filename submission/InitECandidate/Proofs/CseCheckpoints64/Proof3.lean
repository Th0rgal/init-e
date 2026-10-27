import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints64.Proof2
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints64
theorem node192_eq : WordCse.wordCse knowledge96 InitECandidate.Proofs.WordStages.word64_2_582 = (knowledge97, InitECandidate.Proofs.WordStages.word64_4_510) := by
  rw [knowledge96_def, knowledge97_def]
  kernel_rfl
theorem node193_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_511 = (knowledge97, InitECandidate.Proofs.WordStages.word64_4_511) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node191_eq node192_eq
theorem node194_eq : WordCse.wordCse knowledge97 InitECandidate.Proofs.WordStages.word64_2_586 = (knowledge98, InitECandidate.Proofs.WordStages.word64_2_586) := by
  rw [knowledge97_def, knowledge98_def]
  kernel_rfl
theorem node195_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_513 = (knowledge98, InitECandidate.Proofs.WordStages.word64_4_513) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node193_eq node194_eq
theorem node196_eq : WordCse.wordCse knowledge98 InitECandidate.Proofs.WordStages.word64_2_590 = (knowledge99, InitECandidate.Proofs.WordStages.word64_2_590) := by
  rw [knowledge98_def, knowledge99_def]
  kernel_rfl
theorem node197_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_517 = (knowledge99, InitECandidate.Proofs.WordStages.word64_4_517) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node195_eq node196_eq
theorem node198_eq : WordCse.wordCse knowledge99 InitECandidate.Proofs.WordStages.word64_2_598 = (knowledge100, InitECandidate.Proofs.WordStages.word64_4_524) := by
  rw [knowledge99_def, knowledge100_def]
  kernel_rfl
theorem node199_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_525 = (knowledge100, InitECandidate.Proofs.WordStages.word64_4_525) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node197_eq node198_eq
theorem node200_eq : WordCse.wordCse knowledge100 InitECandidate.Proofs.WordStages.word64_2_602 = (knowledge101, InitECandidate.Proofs.WordStages.word64_2_602) := by
  rw [knowledge100_def, knowledge101_def]
  kernel_rfl
theorem node201_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_527 = (knowledge101, InitECandidate.Proofs.WordStages.word64_4_527) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node199_eq node200_eq
theorem node202_eq : WordCse.wordCse knowledge101 InitECandidate.Proofs.WordStages.word64_2_606 = (knowledge102, InitECandidate.Proofs.WordStages.word64_2_606) := by
  rw [knowledge101_def, knowledge102_def]
  kernel_rfl
theorem node203_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_531 = (knowledge102, InitECandidate.Proofs.WordStages.word64_4_531) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node201_eq node202_eq
theorem node204_eq : WordCse.wordCse knowledge102 InitECandidate.Proofs.WordStages.word64_2_614 = (knowledge103, InitECandidate.Proofs.WordStages.word64_4_538) := by
  rw [knowledge102_def, knowledge103_def]
  kernel_rfl
theorem node205_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_539 = (knowledge103, InitECandidate.Proofs.WordStages.word64_4_539) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node203_eq node204_eq
theorem node206_eq : WordCse.wordCse knowledge103 InitECandidate.Proofs.WordStages.word64_2_618 = (knowledge104, InitECandidate.Proofs.WordStages.word64_2_618) := by
  rw [knowledge103_def, knowledge104_def]
  kernel_rfl
theorem node207_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_541 = (knowledge104, InitECandidate.Proofs.WordStages.word64_4_541) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node205_eq node206_eq
theorem node208_eq : WordCse.wordCse knowledge104 InitECandidate.Proofs.WordStages.word64_2_622 = (knowledge105, InitECandidate.Proofs.WordStages.word64_2_622) := by
  rw [knowledge104_def, knowledge105_def]
  kernel_rfl
theorem node209_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_545 = (knowledge105, InitECandidate.Proofs.WordStages.word64_4_545) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node207_eq node208_eq
theorem node210_eq : WordCse.wordCse knowledge105 InitECandidate.Proofs.WordStages.word64_2_630 = (knowledge106, InitECandidate.Proofs.WordStages.word64_4_552) := by
  rw [knowledge105_def, knowledge106_def]
  kernel_rfl
theorem node211_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_553 = (knowledge106, InitECandidate.Proofs.WordStages.word64_4_553) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node209_eq node210_eq
theorem node212_eq : WordCse.wordCse knowledge106 InitECandidate.Proofs.WordStages.word64_2_634 = (knowledge107, InitECandidate.Proofs.WordStages.word64_2_634) := by
  rw [knowledge106_def, knowledge107_def]
  kernel_rfl
theorem node213_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_555 = (knowledge107, InitECandidate.Proofs.WordStages.word64_4_555) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node211_eq node212_eq
theorem node214_eq : WordCse.wordCse knowledge107 InitECandidate.Proofs.WordStages.word64_2_638 = (knowledge108, InitECandidate.Proofs.WordStages.word64_2_638) := by
  rw [knowledge107_def, knowledge108_def]
  kernel_rfl
theorem node215_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_559 = (knowledge108, InitECandidate.Proofs.WordStages.word64_4_559) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node213_eq node214_eq
theorem node216_eq : WordCse.wordCse knowledge108 InitECandidate.Proofs.WordStages.word64_2_646 = (knowledge109, InitECandidate.Proofs.WordStages.word64_4_566) := by
  rw [knowledge108_def, knowledge109_def]
  kernel_rfl
theorem node217_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_567 = (knowledge109, InitECandidate.Proofs.WordStages.word64_4_567) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node215_eq node216_eq
theorem node218_eq : WordCse.wordCse knowledge109 InitECandidate.Proofs.WordStages.word64_2_650 = (knowledge110, InitECandidate.Proofs.WordStages.word64_2_650) := by
  rw [knowledge109_def, knowledge110_def]
  kernel_rfl
theorem node219_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_569 = (knowledge110, InitECandidate.Proofs.WordStages.word64_4_569) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node217_eq node218_eq
theorem node220_eq : WordCse.wordCse knowledge110 InitECandidate.Proofs.WordStages.word64_2_654 = (knowledge111, InitECandidate.Proofs.WordStages.word64_2_654) := by
  rw [knowledge110_def, knowledge111_def]
  kernel_rfl
theorem node221_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_573 = (knowledge111, InitECandidate.Proofs.WordStages.word64_4_573) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node219_eq node220_eq
theorem node222_eq : WordCse.wordCse knowledge111 InitECandidate.Proofs.WordStages.word64_2_662 = (knowledge112, InitECandidate.Proofs.WordStages.word64_4_580) := by
  rw [knowledge111_def, knowledge112_def]
  kernel_rfl
theorem node223_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_581 = (knowledge112, InitECandidate.Proofs.WordStages.word64_4_581) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node221_eq node222_eq
theorem node224_eq : WordCse.wordCse knowledge112 InitECandidate.Proofs.WordStages.word64_2_666 = (knowledge113, InitECandidate.Proofs.WordStages.word64_2_666) := by
  rw [knowledge112_def, knowledge113_def]
  kernel_rfl
theorem node225_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_583 = (knowledge113, InitECandidate.Proofs.WordStages.word64_4_583) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node223_eq node224_eq
theorem node226_eq : WordCse.wordCse knowledge113 InitECandidate.Proofs.WordStages.word64_2_670 = (knowledge114, InitECandidate.Proofs.WordStages.word64_2_670) := by
  rw [knowledge113_def, knowledge114_def]
  kernel_rfl
theorem node227_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_587 = (knowledge114, InitECandidate.Proofs.WordStages.word64_4_587) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node225_eq node226_eq
theorem node228_eq : WordCse.wordCse knowledge114 InitECandidate.Proofs.WordStages.word64_2_678 = (knowledge115, InitECandidate.Proofs.WordStages.word64_4_594) := by
  rw [knowledge114_def, knowledge115_def]
  kernel_rfl
theorem node229_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_595 = (knowledge115, InitECandidate.Proofs.WordStages.word64_4_595) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node227_eq node228_eq
theorem node230_eq : WordCse.wordCse knowledge115 InitECandidate.Proofs.WordStages.word64_2_682 = (knowledge116, InitECandidate.Proofs.WordStages.word64_2_682) := by
  rw [knowledge115_def, knowledge116_def]
  kernel_rfl
theorem node231_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_597 = (knowledge116, InitECandidate.Proofs.WordStages.word64_4_597) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node229_eq node230_eq
theorem node232_eq : WordCse.wordCse knowledge116 InitECandidate.Proofs.WordStages.word64_2_686 = (knowledge117, InitECandidate.Proofs.WordStages.word64_2_686) := by
  rw [knowledge116_def, knowledge117_def]
  kernel_rfl
theorem node233_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_601 = (knowledge117, InitECandidate.Proofs.WordStages.word64_4_601) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node231_eq node232_eq
theorem node234_eq : WordCse.wordCse knowledge117 InitECandidate.Proofs.WordStages.word64_2_694 = (knowledge118, InitECandidate.Proofs.WordStages.word64_4_608) := by
  rw [knowledge117_def, knowledge118_def]
  kernel_rfl
theorem node235_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_609 = (knowledge118, InitECandidate.Proofs.WordStages.word64_4_609) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node233_eq node234_eq
theorem node236_eq : WordCse.wordCse knowledge118 InitECandidate.Proofs.WordStages.word64_2_698 = (knowledge119, InitECandidate.Proofs.WordStages.word64_2_698) := by
  rw [knowledge118_def, knowledge119_def]
  kernel_rfl
theorem node237_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_611 = (knowledge119, InitECandidate.Proofs.WordStages.word64_4_611) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node235_eq node236_eq
theorem node238_eq : WordCse.wordCse knowledge119 InitECandidate.Proofs.WordStages.word64_2_702 = (knowledge120, InitECandidate.Proofs.WordStages.word64_2_702) := by
  rw [knowledge119_def, knowledge120_def]
  kernel_rfl
theorem node239_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_615 = (knowledge120, InitECandidate.Proofs.WordStages.word64_4_615) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node237_eq node238_eq
theorem node240_eq : WordCse.wordCse knowledge120 InitECandidate.Proofs.WordStages.word64_2_710 = (knowledge121, InitECandidate.Proofs.WordStages.word64_4_622) := by
  rw [knowledge120_def, knowledge121_def]
  kernel_rfl
theorem node241_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_623 = (knowledge121, InitECandidate.Proofs.WordStages.word64_4_623) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node239_eq node240_eq
theorem node242_eq : WordCse.wordCse knowledge121 InitECandidate.Proofs.WordStages.word64_2_714 = (knowledge122, InitECandidate.Proofs.WordStages.word64_2_714) := by
  rw [knowledge121_def, knowledge122_def]
  kernel_rfl
theorem node243_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_625 = (knowledge122, InitECandidate.Proofs.WordStages.word64_4_625) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node241_eq node242_eq
theorem node244_eq : WordCse.wordCse knowledge122 InitECandidate.Proofs.WordStages.word64_2_718 = (knowledge123, InitECandidate.Proofs.WordStages.word64_2_718) := by
  rw [knowledge122_def, knowledge123_def]
  kernel_rfl
theorem node245_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_629 = (knowledge123, InitECandidate.Proofs.WordStages.word64_4_629) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node243_eq node244_eq
theorem node246_eq : WordCse.wordCse knowledge123 InitECandidate.Proofs.WordStages.word64_2_726 = (knowledge124, InitECandidate.Proofs.WordStages.word64_4_636) := by
  rw [knowledge123_def, knowledge124_def]
  kernel_rfl
theorem node247_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_637 = (knowledge124, InitECandidate.Proofs.WordStages.word64_4_637) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node245_eq node246_eq
theorem node248_eq : WordCse.wordCse knowledge124 InitECandidate.Proofs.WordStages.word64_2_730 = (knowledge125, InitECandidate.Proofs.WordStages.word64_2_730) := by
  rw [knowledge124_def, knowledge125_def]
  kernel_rfl
theorem node249_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_639 = (knowledge125, InitECandidate.Proofs.WordStages.word64_4_639) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node247_eq node248_eq
theorem node250_eq : WordCse.wordCse knowledge125 InitECandidate.Proofs.WordStages.word64_2_734 = (knowledge126, InitECandidate.Proofs.WordStages.word64_2_734) := by
  rw [knowledge125_def, knowledge126_def]
  kernel_rfl
theorem node251_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_643 = (knowledge126, InitECandidate.Proofs.WordStages.word64_4_643) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node249_eq node250_eq
theorem node252_eq : WordCse.wordCse knowledge126 InitECandidate.Proofs.WordStages.word64_2_742 = (knowledge127, InitECandidate.Proofs.WordStages.word64_4_650) := by
  rw [knowledge126_def, knowledge127_def]
  kernel_rfl
theorem node253_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_651 = (knowledge127, InitECandidate.Proofs.WordStages.word64_4_651) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node251_eq node252_eq
theorem node254_eq : WordCse.wordCse knowledge127 InitECandidate.Proofs.WordStages.word64_2_746 = (knowledge128, InitECandidate.Proofs.WordStages.word64_2_746) := by
  rw [knowledge127_def, knowledge128_def]
  kernel_rfl
theorem node255_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word64_3_653 = (knowledge128, InitECandidate.Proofs.WordStages.word64_4_653) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node253_eq node254_eq
end InitECandidate.Proofs.CseCheckpoints64
