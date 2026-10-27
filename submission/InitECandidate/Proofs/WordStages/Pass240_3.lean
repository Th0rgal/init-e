import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass240_2
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word240_3_471 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_183 word240_2_184

def word240_3_472 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_471 word240_2_187

def word240_3_473 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_198 word240_2_199

def word240_3_474 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word240_3_472, 240, 2)) (some 69) ([]) (some (2, word240_3_473, 240, 3))

def word240_3_475 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_181 word240_3_474

def word240_3_476 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_475 word240_0_3

def word240_3_477 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_214 word240_2_215

def word240_3_478 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_477 word240_2_220

def word240_3_479 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_228 word240_2_231

def word240_3_480 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
            (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word240_3_478, 240, 4)) (some 68) ([2]) (some (2, word240_3_479, 240, 5))

def word240_3_481 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_213 word240_3_480

def word240_3_482 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_212 word240_3_481

def word240_3_483 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_211 word240_3_482

def word240_3_484 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_476 word240_3_483

def word240_3_485 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_484 word240_0_3

def word240_3_486 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_485 word240_2_241

def word240_3_487 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_486 word240_2_243

def word240_3_488 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_487 word240_2_245

def word240_3_489 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word240_2_249, 240, 6)) (some 237) ([2, 4, 6]) (some (2, word240_2_263, 240, 7))

def word240_3_490 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_248 word240_3_489

def word240_3_491 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_247 word240_3_490

def word240_3_492 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_488 word240_3_491

def word240_3_493 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_492 word240_0_3

def word240_3_494 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_493 word240_2_277

def word240_3_495 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_494 word240_2_279

def word240_3_496 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word240_2_286, 240, 8)) (some 78) ([2, 4]) (some (2, word240_2_300, 240, 9))

def word240_3_497 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_285 word240_3_496

def word240_3_498 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_284 word240_3_497

def word240_3_499 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_283 word240_3_498

def word240_3_500 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_495 word240_3_499

def word240_3_501 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_500 word240_0_3

def word240_3_502 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_501 word240_2_313

def word240_3_503 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_502 word240_0_3

def word240_3_504 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_2_331

def word240_3_505 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_504 word240_2_333

def word240_3_506 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_505 word240_2_341

def word240_3_507 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_506 word240_2_355

def word240_3_508 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_507 word240_2_357

def word240_3_509 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_508 word240_2_361

def word240_3_510 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_509 word240_2_363

def word240_3_511 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_510 word240_2_366

def word240_3_512 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(477, 461), (473, 421)]

def word240_3_513 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_511 word240_3_512

def word240_3_514 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_0_63

def word240_3_515 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(477, 377), (473, 373)]

def word240_3_516 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_514 word240_3_515

def word240_3_517 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 377 (Flapjack.WordRegImm.reg 381) word240_3_513 word240_3_516

def word240_3_518 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_320 word240_3_517

def word240_3_519 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_518 word240_0_3

def word240_3_520 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_519 word240_2_394

def word240_3_521 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word240_3_520 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word240_3_522 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_316 word240_3_521

def word240_3_523 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_503 word240_3_522

def word240_3_524 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_523 word240_0_3

def word240_3_525 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_524 word240_2_400

def word240_3_526 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_525 word240_2_402

def word240_3_527 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_526 word240_2_404

def word240_3_528 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))))
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))))
          Flapjack.Spt.ln))),
  Flapjack.Spt.ln)), word240_2_408, 240, 10)) (some 154) ([2, 4, 6]) (some (2, word240_2_422, 240, 11))

def word240_3_529 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_407 word240_3_528

def word240_3_530 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_406 word240_3_529

def word240_3_531 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_527 word240_3_530

def word240_3_532 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_531 word240_0_3

def word240_3_533 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_532 word240_2_434

def word240_3_534 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word240_2_438, 240, 12)) (some 70) ([2]) (some (2, word240_2_452, 240, 13))

def word240_3_535 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_437 word240_3_534

def word240_3_536 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_436 word240_3_535

def word240_3_537 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_533 word240_3_536

def word240_3_538 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_537 word240_0_3

def word240_3_539 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_538 word240_2_464

def word240_3_540 : WordLangProgHOL (BitVec 64) :=
.seq word240_3_539 word240_2_468

def word240_3_541 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_180 word240_3_540

def pass240_3 : WordLangProgHOL (BitVec 64) :=
word240_3_541
theorem pass240_3_eq : WordAlloc.removeDeadProg (pass240_2) = pass240_3 := by
  kernel_rfl
#print axioms pass240_3_eq
end InitECandidate.Proofs.WordStages
