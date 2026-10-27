import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass270_7
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word270_8_426 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(41, 4), (37, 2), (25, 0)]

def word270_8_427 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(97, 4), (93, 2), (69, 55), (73, 59), (77, 63)]

def word270_8_428 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (69, 55), (73, 59), (77, 63)]

def word270_8_429 : WordLangProgHOL (BitVec 64) :=
.seq word270_8_428 word270_2_178

def word270_8_430 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))))),
  Flapjack.Spt.ln)), word270_8_427, 270, 2)) (some 269) ([2, 4, 6]) (some (2, word270_8_429, 270, 3))

def word270_8_431 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(169, 241), (173, 197), (181, 249), (189, 213)]

def word270_8_432 : WordLangProgHOL (BitVec 64) :=
.seq word270_8_431 word270_0_57

def word270_8_433 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_269 word270_8_432

def word270_8_434 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_391 word270_8_433

def word270_8_435 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_262 word270_8_434

def word270_8_436 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_260 word270_8_435

def word270_8_437 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_390 word270_8_436

def word270_8_438 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_256 word270_8_437

def word270_8_439 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_252 word270_8_438

def word270_8_440 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_389 word270_8_439

def word270_8_441 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_8_440

def word270_8_442 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 193 (Flapjack.WordRegImm.reg 197) word270_8_441 word270_3_349

def word270_8_443 : WordLangProgHOL (BitVec 64) :=
.seq word270_8_442 word270_7_404

def word270_8_444 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_388 word270_8_443

def word270_8_445 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          Flapjack.Spt.ln)))
    Flapjack.Spt.ln)) word270_8_444 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    Flapjack.Spt.ln))

def word270_8_446 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 169)]

def word270_8_447 : WordLangProgHOL (BitVec 64) :=
.seq word270_8_446 word270_2_312

def word270_8_448 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_8_447

def word270_8_449 : WordLangProgHOL (BitVec 64) :=
.seq word270_8_445 word270_8_448

def word270_8_450 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_241 word270_8_449

def word270_8_451 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_8_450

def word270_8_452 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_238 word270_8_451

def word270_8_453 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_236 word270_8_452

def word270_8_454 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_8_453

def word270_8_455 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_8_454

def word270_8_456 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_387 word270_8_455

def word270_8_457 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_197 word270_8_456

def word270_8_458 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_195 word270_8_457

def word270_8_459 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_8_458

def word270_8_460 : WordLangProgHOL (BitVec 64) :=
.seq word270_8_430 word270_8_459

def word270_8_461 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_377 word270_8_460

def word270_8_462 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_159 word270_8_461

def word270_8_463 : WordLangProgHOL (BitVec 64) :=
.seq word270_8_426 word270_8_462

def pass270_8 : WordLangProgHOL (BitVec 64) :=
word270_8_463
theorem pass270_8_eq : WordAlloc.removeDeadProg (pass270_7) = pass270_8 := by
  kernel_rfl
#print axioms pass270_8_eq
end InitECandidate.Proofs.WordStages
