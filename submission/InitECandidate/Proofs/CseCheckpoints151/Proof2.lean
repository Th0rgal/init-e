import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CseCheckpoints151.Proof1
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
namespace InitECandidate.Proofs.CseCheckpoints151
theorem node128_eq : WordCse.wordCse knowledge64 InitECandidate.Proofs.WordStages.word151_2_372 = (knowledge65, InitECandidate.Proofs.WordStages.word151_2_372) := by
  rw [knowledge64_def, knowledge65_def]
  kernel_rfl
theorem node129_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_373 = (knowledge65, InitECandidate.Proofs.WordStages.word151_2_373) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node127_eq node128_eq
theorem node130_eq : WordCse.wordCse knowledge65 InitECandidate.Proofs.WordStages.word151_2_392 = (knowledge66, InitECandidate.Proofs.WordStages.word151_2_392) := by
  rw [knowledge65_def, knowledge66_def]
  kernel_rfl
theorem node131_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_393 = (knowledge66, InitECandidate.Proofs.WordStages.word151_2_393) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node129_eq node130_eq
theorem node132_eq : WordCse.wordCse knowledge66 InitECandidate.Proofs.WordStages.word151_2_396 = (knowledge67, InitECandidate.Proofs.WordStages.word151_2_396) := by
  rw [knowledge66_def, knowledge67_def]
  kernel_rfl
theorem node133_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_397 = (knowledge67, InitECandidate.Proofs.WordStages.word151_2_397) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node131_eq node132_eq
theorem node134_eq : WordCse.wordCse knowledge67 InitECandidate.Proofs.WordStages.word151_2_398 = (knowledge68, InitECandidate.Proofs.WordStages.word151_2_398) := by
  rw [knowledge67_def, knowledge68_def]
  kernel_rfl
theorem node135_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_399 = (knowledge68, InitECandidate.Proofs.WordStages.word151_2_399) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node133_eq node134_eq
theorem node136_eq : WordCse.wordCse knowledge68 InitECandidate.Proofs.WordStages.word151_2_402 = (knowledge69, InitECandidate.Proofs.WordStages.word151_2_402) := by
  rw [knowledge68_def, knowledge69_def]
  kernel_rfl
theorem node137_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_403 = (knowledge69, InitECandidate.Proofs.WordStages.word151_2_403) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node135_eq node136_eq
theorem node138_eq : WordCse.wordCse knowledge69 InitECandidate.Proofs.WordStages.word151_2_404 = (knowledge70, InitECandidate.Proofs.WordStages.word151_2_404) := by
  rw [knowledge69_def, knowledge70_def]
  kernel_rfl
theorem node139_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_405 = (knowledge70, InitECandidate.Proofs.WordStages.word151_2_405) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node137_eq node138_eq
theorem node140_eq : WordCse.wordCse knowledge70 InitECandidate.Proofs.WordStages.word151_2_408 = (knowledge71, InitECandidate.Proofs.WordStages.word151_2_408) := by
  rw [knowledge70_def, knowledge71_def]
  kernel_rfl
theorem node141_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_409 = (knowledge71, InitECandidate.Proofs.WordStages.word151_2_409) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node139_eq node140_eq
theorem node142_eq : WordCse.wordCse knowledge71 InitECandidate.Proofs.WordStages.word151_2_410 = (knowledge72, InitECandidate.Proofs.WordStages.word151_2_410) := by
  rw [knowledge71_def, knowledge72_def]
  kernel_rfl
theorem node143_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_411 = (knowledge72, InitECandidate.Proofs.WordStages.word151_2_411) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node141_eq node142_eq
theorem node144_eq : WordCse.wordCse knowledge72 InitECandidate.Proofs.WordStages.word151_2_414 = (knowledge73, InitECandidate.Proofs.WordStages.word151_2_414) := by
  rw [knowledge72_def, knowledge73_def]
  kernel_rfl
theorem node145_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_415 = (knowledge73, InitECandidate.Proofs.WordStages.word151_2_415) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node143_eq node144_eq
theorem node146_eq : WordCse.wordCse knowledge73 InitECandidate.Proofs.WordStages.word151_2_416 = (knowledge74, InitECandidate.Proofs.WordStages.word151_2_416) := by
  rw [knowledge73_def, knowledge74_def]
  kernel_rfl
theorem node147_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_417 = (knowledge74, InitECandidate.Proofs.WordStages.word151_2_417) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node145_eq node146_eq
theorem node148_eq : WordCse.wordCse knowledge74 InitECandidate.Proofs.WordStages.word151_2_436 = (knowledge75, InitECandidate.Proofs.WordStages.word151_2_436) := by
  rw [knowledge74_def, knowledge75_def]
  kernel_rfl
theorem node149_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_437 = (knowledge75, InitECandidate.Proofs.WordStages.word151_2_437) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node147_eq node148_eq
theorem node150_eq : WordCse.wordCse knowledge75 InitECandidate.Proofs.WordStages.word151_2_440 = (knowledge76, InitECandidate.Proofs.WordStages.word151_2_440) := by
  rw [knowledge75_def, knowledge76_def]
  kernel_rfl
theorem node151_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_441 = (knowledge76, InitECandidate.Proofs.WordStages.word151_2_441) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node149_eq node150_eq
theorem node152_eq : WordCse.wordCse knowledge76 InitECandidate.Proofs.WordStages.word151_2_442 = (knowledge77, InitECandidate.Proofs.WordStages.word151_2_442) := by
  rw [knowledge76_def, knowledge77_def]
  kernel_rfl
theorem node153_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_443 = (knowledge77, InitECandidate.Proofs.WordStages.word151_2_443) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node151_eq node152_eq
theorem node154_eq : WordCse.wordCse knowledge77 InitECandidate.Proofs.WordStages.word151_2_446 = (knowledge78, InitECandidate.Proofs.WordStages.word151_2_446) := by
  rw [knowledge77_def, knowledge78_def]
  kernel_rfl
theorem node155_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_447 = (knowledge78, InitECandidate.Proofs.WordStages.word151_2_447) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node153_eq node154_eq
theorem node156_eq : WordCse.wordCse knowledge78 InitECandidate.Proofs.WordStages.word151_2_448 = (knowledge79, InitECandidate.Proofs.WordStages.word151_2_448) := by
  rw [knowledge78_def, knowledge79_def]
  kernel_rfl
theorem node157_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_449 = (knowledge79, InitECandidate.Proofs.WordStages.word151_2_449) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node155_eq node156_eq
theorem node158_eq : WordCse.wordCse knowledge79 InitECandidate.Proofs.WordStages.word151_2_452 = (knowledge80, InitECandidate.Proofs.WordStages.word151_2_452) := by
  rw [knowledge79_def, knowledge80_def]
  kernel_rfl
theorem node159_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_453 = (knowledge80, InitECandidate.Proofs.WordStages.word151_2_453) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node157_eq node158_eq
theorem node160_eq : WordCse.wordCse knowledge80 InitECandidate.Proofs.WordStages.word151_2_454 = (knowledge81, InitECandidate.Proofs.WordStages.word151_2_454) := by
  rw [knowledge80_def, knowledge81_def]
  kernel_rfl
theorem node161_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_455 = (knowledge81, InitECandidate.Proofs.WordStages.word151_2_455) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node159_eq node160_eq
theorem node162_eq : WordCse.wordCse knowledge81 InitECandidate.Proofs.WordStages.word151_2_458 = (knowledge82, InitECandidate.Proofs.WordStages.word151_2_458) := by
  rw [knowledge81_def, knowledge82_def]
  kernel_rfl
theorem node163_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_459 = (knowledge82, InitECandidate.Proofs.WordStages.word151_2_459) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node161_eq node162_eq
theorem node164_eq : WordCse.wordCse knowledge82 InitECandidate.Proofs.WordStages.word151_2_460 = (knowledge83, InitECandidate.Proofs.WordStages.word151_2_460) := by
  rw [knowledge82_def, knowledge83_def]
  kernel_rfl
theorem node165_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_461 = (knowledge83, InitECandidate.Proofs.WordStages.word151_2_461) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node163_eq node164_eq
theorem node166_eq : WordCse.wordCse knowledge83 InitECandidate.Proofs.WordStages.word151_2_480 = (knowledge84, InitECandidate.Proofs.WordStages.word151_2_480) := by
  rw [knowledge83_def, knowledge84_def]
  kernel_rfl
theorem node167_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_481 = (knowledge84, InitECandidate.Proofs.WordStages.word151_2_481) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node165_eq node166_eq
theorem node168_eq : WordCse.wordCse knowledge84 InitECandidate.Proofs.WordStages.word151_2_484 = (knowledge85, InitECandidate.Proofs.WordStages.word151_2_484) := by
  rw [knowledge84_def, knowledge85_def]
  kernel_rfl
theorem node169_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_485 = (knowledge85, InitECandidate.Proofs.WordStages.word151_2_485) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node167_eq node168_eq
theorem node170_eq : WordCse.wordCse knowledge85 InitECandidate.Proofs.WordStages.word151_2_486 = (knowledge86, InitECandidate.Proofs.WordStages.word151_2_486) := by
  rw [knowledge85_def, knowledge86_def]
  kernel_rfl
theorem node171_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_487 = (knowledge86, InitECandidate.Proofs.WordStages.word151_2_487) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node169_eq node170_eq
theorem node172_eq : WordCse.wordCse knowledge86 InitECandidate.Proofs.WordStages.word151_2_490 = (knowledge87, InitECandidate.Proofs.WordStages.word151_2_490) := by
  rw [knowledge86_def, knowledge87_def]
  kernel_rfl
theorem node173_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_491 = (knowledge87, InitECandidate.Proofs.WordStages.word151_2_491) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node171_eq node172_eq
theorem node174_eq : WordCse.wordCse knowledge87 InitECandidate.Proofs.WordStages.word151_2_492 = (knowledge88, InitECandidate.Proofs.WordStages.word151_2_492) := by
  rw [knowledge87_def, knowledge88_def]
  kernel_rfl
theorem node175_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_493 = (knowledge88, InitECandidate.Proofs.WordStages.word151_2_493) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node173_eq node174_eq
theorem node176_eq : WordCse.wordCse knowledge88 InitECandidate.Proofs.WordStages.word151_2_496 = (knowledge89, InitECandidate.Proofs.WordStages.word151_2_496) := by
  rw [knowledge88_def, knowledge89_def]
  kernel_rfl
theorem node177_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_497 = (knowledge89, InitECandidate.Proofs.WordStages.word151_2_497) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node175_eq node176_eq
theorem node178_eq : WordCse.wordCse knowledge89 InitECandidate.Proofs.WordStages.word151_2_498 = (knowledge90, InitECandidate.Proofs.WordStages.word151_2_498) := by
  rw [knowledge89_def, knowledge90_def]
  kernel_rfl
theorem node179_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_499 = (knowledge90, InitECandidate.Proofs.WordStages.word151_2_499) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node177_eq node178_eq
theorem node180_eq : WordCse.wordCse knowledge90 InitECandidate.Proofs.WordStages.word151_2_502 = (knowledge91, InitECandidate.Proofs.WordStages.word151_2_502) := by
  rw [knowledge90_def, knowledge91_def]
  kernel_rfl
theorem node181_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_503 = (knowledge91, InitECandidate.Proofs.WordStages.word151_2_503) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node179_eq node180_eq
theorem node182_eq : WordCse.wordCse knowledge91 InitECandidate.Proofs.WordStages.word151_2_504 = (knowledge92, InitECandidate.Proofs.WordStages.word151_2_504) := by
  rw [knowledge91_def, knowledge92_def]
  kernel_rfl
theorem node183_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_505 = (knowledge92, InitECandidate.Proofs.WordStages.word151_2_505) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node181_eq node182_eq
theorem node184_eq : WordCse.wordCse knowledge92 InitECandidate.Proofs.WordStages.word151_2_524 = (knowledge93, InitECandidate.Proofs.WordStages.word151_2_524) := by
  rw [knowledge92_def, knowledge93_def]
  kernel_rfl
theorem node185_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_525 = (knowledge93, InitECandidate.Proofs.WordStages.word151_2_525) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node183_eq node184_eq
theorem node186_eq : WordCse.wordCse knowledge93 InitECandidate.Proofs.WordStages.word151_2_528 = (knowledge94, InitECandidate.Proofs.WordStages.word151_2_528) := by
  rw [knowledge93_def, knowledge94_def]
  kernel_rfl
theorem node187_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_529 = (knowledge94, InitECandidate.Proofs.WordStages.word151_2_529) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node185_eq node186_eq
theorem node188_eq : WordCse.wordCse knowledge94 InitECandidate.Proofs.WordStages.word151_2_530 = (knowledge95, InitECandidate.Proofs.WordStages.word151_2_530) := by
  rw [knowledge94_def, knowledge95_def]
  kernel_rfl
theorem node189_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_531 = (knowledge95, InitECandidate.Proofs.WordStages.word151_2_531) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node187_eq node188_eq
theorem node190_eq : WordCse.wordCse knowledge95 InitECandidate.Proofs.WordStages.word151_2_534 = (knowledge96, InitECandidate.Proofs.WordStages.word151_2_534) := by
  rw [knowledge95_def, knowledge96_def]
  kernel_rfl
theorem node191_eq : WordCse.wordCse knowledge0 InitECandidate.Proofs.WordStages.word151_2_535 = (knowledge96, InitECandidate.Proofs.WordStages.word151_2_535) := by
  exact InitECandidate.Proofs.CseComputation.seq_of_eq _ _ _ _ _ _ _ node189_eq node190_eq
end InitECandidate.Proofs.CseCheckpoints151
