import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass240_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word240_4_542 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(417, 397)]

def word240_4_543 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_335 word240_4_542

def word240_4_544 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(425, 405)]

def word240_4_545 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_338 word240_4_544

def word240_4_546 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_543 word240_4_545

def word240_4_547 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_505 word240_4_546

def word240_4_548 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_547 word240_2_355

def word240_4_549 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_548 word240_2_357

def word240_4_550 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_549 word240_2_361

def word240_4_551 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_550 word240_2_363

def word240_4_552 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_551 word240_2_366

def word240_4_553 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_552 word240_3_512

def word240_4_554 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 377 (Flapjack.WordRegImm.reg 381) word240_4_553 word240_3_516

def word240_4_555 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_320 word240_4_554

def word240_4_556 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_555 word240_0_3

def word240_4_557 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_556 word240_2_394

def word240_4_558 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln))))
    Flapjack.Spt.ln)) word240_4_557 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    Flapjack.Spt.ln))

def word240_4_559 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_316 word240_4_558

def word240_4_560 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_503 word240_4_559

def word240_4_561 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_560 word240_0_3

def word240_4_562 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_561 word240_2_400

def word240_4_563 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_562 word240_2_402

def word240_4_564 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_563 word240_2_404

def word240_4_565 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_564 word240_3_530

def word240_4_566 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_565 word240_0_3

def word240_4_567 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_566 word240_2_434

def word240_4_568 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_567 word240_3_536

def word240_4_569 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_568 word240_0_3

def word240_4_570 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_569 word240_2_464

def word240_4_571 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_570 word240_2_468

def word240_4_572 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_180 word240_4_571

def pass240_4 : WordLangProgHOL (BitVec 64) :=
word240_4_572
theorem pass240_4_eq : WordCse.wordCommonSubexpElim (pass240_3) = pass240_4 := by
  kernel_rfl
#print axioms pass240_4_eq
end InitECandidate.Proofs.WordStages
