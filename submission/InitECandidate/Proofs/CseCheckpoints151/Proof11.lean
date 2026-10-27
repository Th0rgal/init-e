import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof10
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node704_eq : WordCse.wordCse knowledge352 InitECandidate.Proofs.WordStages.word151_2_6382 = (knowledge353, InitECandidate.Proofs.WordStages.word151_2_6382) := by
  rw [knowledge352_def, knowledge353_def]
  kernel_rfl
theorem node705_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6383 = (knowledge353, program13511) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node703_eq node704_eq
theorem node706_eq : WordCse.wordCse knowledge353 InitECandidate.Proofs.WordStages.word151_2_6444 = (knowledge354, program13520) := by
  rw [knowledge353_def, knowledge354_def]
  kernel_rfl
theorem node707_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6445 = (knowledge354, program13521) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node705_eq node706_eq
theorem node708_eq : WordCse.wordCse knowledge354 InitECandidate.Proofs.WordStages.word151_2_6506 = (knowledge355, InitECandidate.Proofs.WordStages.word151_2_6506) := by
  rw [knowledge354_def, knowledge355_def]
  kernel_rfl
theorem node709_eq : WordCse.wordCse knowledge355 InitECandidate.Proofs.WordStages.word151_2_6509 = (knowledge356, InitECandidate.Proofs.WordStages.word151_2_6509) := by
  rw [knowledge355_def, knowledge356_def]
  kernel_rfl
theorem node710_eq : WordCse.wordCse knowledge354 InitECandidate.Proofs.WordStages.word151_2_6510 = (knowledge356, InitECandidate.Proofs.WordStages.word151_2_6510) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node708_eq node709_eq
theorem node711_eq : WordCse.wordCse knowledge356 InitECandidate.Proofs.WordStages.word151_2_6511 = (knowledge357, InitECandidate.Proofs.WordStages.word151_2_6511) := by
  rw [knowledge356_def, knowledge357_def]
  kernel_rfl
theorem node712_eq : WordCse.wordCse knowledge354 InitECandidate.Proofs.WordStages.word151_2_6512 = (knowledge357, InitECandidate.Proofs.WordStages.word151_2_6512) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node710_eq node711_eq
theorem node713_eq : WordCse.wordCse knowledge357 InitECandidate.Proofs.WordStages.word151_2_6513 = (knowledge358, InitECandidate.Proofs.WordStages.word151_2_6513) := by
  rw [knowledge357_def, knowledge358_def]
  kernel_rfl
theorem node714_eq : WordCse.wordCse knowledge354 InitECandidate.Proofs.WordStages.word151_2_6514 = (knowledge358, InitECandidate.Proofs.WordStages.word151_2_6514) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node712_eq node713_eq
theorem node715_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6515 = (knowledge358, program13522) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node707_eq node714_eq
theorem node716_eq : WordCse.wordCse knowledge358 InitECandidate.Proofs.WordStages.word151_2_6516 = (knowledge359, InitECandidate.Proofs.WordStages.word151_2_6516) := by
  rw [knowledge358_def, knowledge359_def]
  kernel_rfl
theorem node717_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6517 = (knowledge359, program13523) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node715_eq node716_eq
theorem node718_eq : WordCse.wordCse knowledge359 InitECandidate.Proofs.WordStages.word151_2_6578 = (knowledge360, InitECandidate.Proofs.WordStages.word151_2_6578) := by
  rw [knowledge359_def, knowledge360_def]
  kernel_rfl
theorem node719_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6579 = (knowledge360, program13524) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node717_eq node718_eq
theorem node720_eq : WordCse.wordCse knowledge360 InitECandidate.Proofs.WordStages.word151_2_6588 = (knowledge361, InitECandidate.Proofs.WordStages.word151_2_6588) := by
  rw [knowledge360_def, knowledge361_def]
  kernel_rfl
theorem node721_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6589 = (knowledge361, program13525) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node719_eq node720_eq
theorem node722_eq : WordCse.wordCse knowledge361 InitECandidate.Proofs.WordStages.word151_2_6590 = (knowledge362, InitECandidate.Proofs.WordStages.word151_2_6590) := by
  rw [knowledge361_def, knowledge362_def]
  kernel_rfl
theorem node723_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6591 = (knowledge362, program13526) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node721_eq node722_eq
theorem node724_eq : WordCse.wordCse knowledge362 InitECandidate.Proofs.WordStages.word151_2_6652 = (knowledge363, program13535) := by
  rw [knowledge362_def, knowledge363_def]
  kernel_rfl
theorem node725_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6653 = (knowledge363, program13536) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node723_eq node724_eq
theorem node726_eq : WordCse.wordCse knowledge363 InitECandidate.Proofs.WordStages.word151_2_6714 = (knowledge364, InitECandidate.Proofs.WordStages.word151_2_6714) := by
  rw [knowledge363_def, knowledge364_def]
  kernel_rfl
theorem node727_eq : WordCse.wordCse knowledge364 InitECandidate.Proofs.WordStages.word151_2_6717 = (knowledge365, InitECandidate.Proofs.WordStages.word151_2_6717) := by
  rw [knowledge364_def, knowledge365_def]
  kernel_rfl
theorem node728_eq : WordCse.wordCse knowledge363 InitECandidate.Proofs.WordStages.word151_2_6718 = (knowledge365, InitECandidate.Proofs.WordStages.word151_2_6718) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node726_eq node727_eq
theorem node729_eq : WordCse.wordCse knowledge365 InitECandidate.Proofs.WordStages.word151_2_6719 = (knowledge366, InitECandidate.Proofs.WordStages.word151_2_6719) := by
  rw [knowledge365_def, knowledge366_def]
  kernel_rfl
theorem node730_eq : WordCse.wordCse knowledge363 InitECandidate.Proofs.WordStages.word151_2_6720 = (knowledge366, InitECandidate.Proofs.WordStages.word151_2_6720) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node728_eq node729_eq
theorem node731_eq : WordCse.wordCse knowledge366 InitECandidate.Proofs.WordStages.word151_2_6721 = (knowledge367, InitECandidate.Proofs.WordStages.word151_2_6721) := by
  rw [knowledge366_def, knowledge367_def]
  kernel_rfl
theorem node732_eq : WordCse.wordCse knowledge363 InitECandidate.Proofs.WordStages.word151_2_6722 = (knowledge367, InitECandidate.Proofs.WordStages.word151_2_6722) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node730_eq node731_eq
theorem node733_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6723 = (knowledge367, program13537) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node725_eq node732_eq
theorem node734_eq : WordCse.wordCse knowledge367 InitECandidate.Proofs.WordStages.word151_2_6724 = (knowledge368, InitECandidate.Proofs.WordStages.word151_2_6724) := by
  rw [knowledge367_def, knowledge368_def]
  kernel_rfl
theorem node735_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6725 = (knowledge368, program13538) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node733_eq node734_eq
theorem node736_eq : WordCse.wordCse knowledge368 InitECandidate.Proofs.WordStages.word151_2_6786 = (knowledge369, InitECandidate.Proofs.WordStages.word151_2_6786) := by
  rw [knowledge368_def, knowledge369_def]
  kernel_rfl
theorem node737_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6787 = (knowledge369, program13539) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node735_eq node736_eq
theorem node738_eq : WordCse.wordCse knowledge369 InitECandidate.Proofs.WordStages.word151_2_6796 = (knowledge370, InitECandidate.Proofs.WordStages.word151_2_6796) := by
  rw [knowledge369_def, knowledge370_def]
  kernel_rfl
theorem node739_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6797 = (knowledge370, program13540) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node737_eq node738_eq
theorem node740_eq : WordCse.wordCse knowledge370 InitECandidate.Proofs.WordStages.word151_2_6798 = (knowledge371, InitECandidate.Proofs.WordStages.word151_2_6798) := by
  rw [knowledge370_def, knowledge371_def]
  kernel_rfl
theorem node741_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6799 = (knowledge371, program13541) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node739_eq node740_eq
theorem node742_eq : WordCse.wordCse knowledge371 InitECandidate.Proofs.WordStages.word151_2_6860 = (knowledge372, program13550) := by
  rw [knowledge371_def, knowledge372_def]
  kernel_rfl
theorem node743_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6861 = (knowledge372, program13551) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node741_eq node742_eq
theorem node744_eq : WordCse.wordCse knowledge372 InitECandidate.Proofs.WordStages.word151_2_6922 = (knowledge373, InitECandidate.Proofs.WordStages.word151_2_6922) := by
  rw [knowledge372_def, knowledge373_def]
  kernel_rfl
theorem node745_eq : WordCse.wordCse knowledge373 InitECandidate.Proofs.WordStages.word151_2_6925 = (knowledge374, InitECandidate.Proofs.WordStages.word151_2_6925) := by
  rw [knowledge373_def, knowledge374_def]
  kernel_rfl
theorem node746_eq : WordCse.wordCse knowledge372 InitECandidate.Proofs.WordStages.word151_2_6926 = (knowledge374, InitECandidate.Proofs.WordStages.word151_2_6926) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node744_eq node745_eq
theorem node747_eq : WordCse.wordCse knowledge374 InitECandidate.Proofs.WordStages.word151_2_6927 = (knowledge375, InitECandidate.Proofs.WordStages.word151_2_6927) := by
  rw [knowledge374_def, knowledge375_def]
  kernel_rfl
theorem node748_eq : WordCse.wordCse knowledge372 InitECandidate.Proofs.WordStages.word151_2_6928 = (knowledge375, InitECandidate.Proofs.WordStages.word151_2_6928) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node746_eq node747_eq
theorem node749_eq : WordCse.wordCse knowledge375 InitECandidate.Proofs.WordStages.word151_2_6929 = (knowledge376, InitECandidate.Proofs.WordStages.word151_2_6929) := by
  rw [knowledge375_def, knowledge376_def]
  kernel_rfl
theorem node750_eq : WordCse.wordCse knowledge372 InitECandidate.Proofs.WordStages.word151_2_6930 = (knowledge376, InitECandidate.Proofs.WordStages.word151_2_6930) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node748_eq node749_eq
theorem node751_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6931 = (knowledge376, program13552) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node743_eq node750_eq
theorem node752_eq : WordCse.wordCse knowledge376 InitECandidate.Proofs.WordStages.word151_2_6932 = (knowledge377, InitECandidate.Proofs.WordStages.word151_2_6932) := by
  rw [knowledge376_def, knowledge377_def]
  kernel_rfl
theorem node753_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6933 = (knowledge377, program13553) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node751_eq node752_eq
theorem node754_eq : WordCse.wordCse knowledge377 InitECandidate.Proofs.WordStages.word151_2_6994 = (knowledge378, InitECandidate.Proofs.WordStages.word151_2_6994) := by
  rw [knowledge377_def, knowledge378_def]
  kernel_rfl
theorem node755_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_6995 = (knowledge378, program13554) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node753_eq node754_eq
theorem node756_eq : WordCse.wordCse knowledge378 InitECandidate.Proofs.WordStages.word151_2_7004 = (knowledge379, InitECandidate.Proofs.WordStages.word151_2_7004) := by
  rw [knowledge378_def, knowledge379_def]
  kernel_rfl
theorem node757_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_7005 = (knowledge379, program13555) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node755_eq node756_eq
theorem node758_eq : WordCse.wordCse knowledge379 InitECandidate.Proofs.WordStages.word151_2_7006 = (knowledge380, InitECandidate.Proofs.WordStages.word151_2_7006) := by
  rw [knowledge379_def, knowledge380_def]
  kernel_rfl
theorem node759_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_7007 = (knowledge380, program13556) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node757_eq node758_eq
theorem node760_eq : WordCse.wordCse knowledge380 InitECandidate.Proofs.WordStages.word151_2_7068 = (knowledge381, program13565) := by
  rw [knowledge380_def, knowledge381_def]
  kernel_rfl
theorem node761_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_7069 = (knowledge381, program13566) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node759_eq node760_eq
theorem node762_eq : WordCse.wordCse knowledge381 InitECandidate.Proofs.WordStages.word151_2_7130 = (knowledge382, InitECandidate.Proofs.WordStages.word151_2_7130) := by
  rw [knowledge381_def, knowledge382_def]
  kernel_rfl
theorem node763_eq : WordCse.wordCse knowledge382 InitECandidate.Proofs.WordStages.word151_2_7133 = (knowledge383, InitECandidate.Proofs.WordStages.word151_2_7133) := by
  rw [knowledge382_def, knowledge383_def]
  kernel_rfl
theorem node764_eq : WordCse.wordCse knowledge381 InitECandidate.Proofs.WordStages.word151_2_7134 = (knowledge383, InitECandidate.Proofs.WordStages.word151_2_7134) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node762_eq node763_eq
theorem node765_eq : WordCse.wordCse knowledge383 InitECandidate.Proofs.WordStages.word151_2_7135 = (knowledge384, InitECandidate.Proofs.WordStages.word151_2_7135) := by
  rw [knowledge383_def, knowledge384_def]
  kernel_rfl
theorem node766_eq : WordCse.wordCse knowledge381 InitECandidate.Proofs.WordStages.word151_2_7136 = (knowledge384, InitECandidate.Proofs.WordStages.word151_2_7136) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node764_eq node765_eq
theorem node767_eq : WordCse.wordCse knowledge384 InitECandidate.Proofs.WordStages.word151_2_7137 = (knowledge385, InitECandidate.Proofs.WordStages.word151_2_7137) := by
  rw [knowledge384_def, knowledge385_def]
  kernel_rfl
end InitECandidate.Proofs.CseCheckpoints151
