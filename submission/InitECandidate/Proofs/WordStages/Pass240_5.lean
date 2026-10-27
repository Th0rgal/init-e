import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass240_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word240_5_573 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(477, 369), (473, 373)]

def word240_5_574 : WordLangProgHOL (BitVec 64) :=
.seq word240_4_552 word240_5_573

def word240_5_575 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 377 (Flapjack.WordRegImm.reg 381) word240_5_574 word240_3_516

def word240_5_576 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_320 word240_5_575

def word240_5_577 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_576 word240_0_3

def word240_5_578 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_577 word240_2_394

def word240_5_579 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word240_5_578 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word240_5_580 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_316 word240_5_579

def word240_5_581 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_503 word240_5_580

def word240_5_582 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_581 word240_0_3

def word240_5_583 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_582 word240_2_400

def word240_5_584 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_583 word240_2_402

def word240_5_585 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_584 word240_2_404

def word240_5_586 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_585 word240_3_530

def word240_5_587 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_586 word240_0_3

def word240_5_588 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_587 word240_2_434

def word240_5_589 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_588 word240_3_536

def word240_5_590 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_589 word240_0_3

def word240_5_591 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_590 word240_2_464

def word240_5_592 : WordLangProgHOL (BitVec 64) :=
.seq word240_5_591 word240_2_468

def word240_5_593 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_180 word240_5_592

def pass240_5 : WordLangProgHOL (BitVec 64) :=
word240_5_593
theorem pass240_5_eq : WordCopy.copyProp (pass240_4) = pass240_5 := by
  kernel_rfl
#print axioms pass240_5_eq
end InitECandidate.Proofs.WordStages
