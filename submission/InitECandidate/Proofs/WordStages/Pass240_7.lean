import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass240_6
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word240_7_594 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(47, 0), (51, 4), (55, 2), (59, 6), (29, 0), (33, 2), (37, 4), (41, 6)]

def word240_7_595 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(89, 2), (81, 2), (65, 47), (69, 51), (73, 55), (77, 59)]

def word240_7_596 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (85, 2), (65, 47), (69, 51), (73, 55), (77, 59)]

def word240_7_597 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_596 word240_2_195

def word240_7_598 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word240_7_595, 240, 2)) (some 69) ([]) (some (2, word240_7_597, 240, 3))

def word240_7_599 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 101), (107, 65), (111, 69), (115, 73), (119, 89), (123, 77)]

def word240_7_600 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(161, 2), (149, 2), (129, 107), (133, 111), (137, 115), (141, 119), (145, 123)]

def word240_7_601 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (153, 2), (129, 107), (133, 111), (137, 115), (141, 119), (145, 123)]

def word240_7_602 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_601 word240_2_195

def word240_7_603 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
            (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word240_7_600, 240, 4)) (some 68) ([2]) (some (2, word240_7_602, 240, 5))

def word240_7_604 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2, 137), (4, 133), (6, 161), (179, 129), (183, 133), (187, 137), (191, 161), (195, 141), (199, 145), (173, 161),
    (169, 133), (165, 137)]

def word240_7_605 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2, 2), (233, 2), (205, 179), (209, 183), (213, 187), (217, 191), (221, 195), (225, 199)]

def word240_7_606 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_605 word240_2_195

def word240_7_607 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word240_2_249, 240, 6)) (some 237) ([2, 4, 6]) (some (2, word240_7_606, 240, 7))

def word240_7_608 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2, 253), (4, 261), (267, 205), (271, 209), (275, 213), (279, 245), (283, 221), (287, 225), (291, 253)]

def word240_7_609 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2, 2), (329, 2), (297, 267), (301, 271), (305, 275), (309, 279), (313, 283), (317, 287), (321, 291)]

def word240_7_610 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_609 word240_2_195

def word240_7_611 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word240_2_286, 240, 8)) (some 78) ([2, 4]) (some (2, word240_7_610, 240, 9))

def word240_7_612 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(381, 349), (377, 369)]

def word240_7_613 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(425, 405), (421, 401), (417, 397), (413, 393)]

def word240_7_614 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(349, 381), (369, 457), (373, 421), (461, 457)]

def word240_7_615 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_614 word240_0_57

def word240_7_616 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_360 word240_7_615

def word240_7_617 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_359 word240_7_616

def word240_7_618 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_357 word240_7_617

def word240_7_619 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_353 word240_7_618

def word240_7_620 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_352 word240_7_619

def word240_7_621 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_348 word240_7_620

def word240_7_622 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_347 word240_7_621

def word240_7_623 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_345 word240_7_622

def word240_7_624 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_344 word240_7_623

def word240_7_625 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_343 word240_7_624

def word240_7_626 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_613 word240_7_625

def word240_7_627 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_333 word240_7_626

def word240_7_628 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_329 word240_7_627

def word240_7_629 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_328 word240_7_628

def word240_7_630 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_326 word240_7_629

def word240_7_631 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_325 word240_7_630

def word240_7_632 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_631

def word240_7_633 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 377 (Flapjack.WordRegImm.reg 381) word240_7_632 word240_3_514

def word240_7_634 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_2_394

def word240_7_635 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_633 word240_7_634

def word240_7_636 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_612 word240_7_635

def word240_7_637 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word240_7_636 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word240_7_638 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2, 357), (4, 373), (6, 365), (519, 345), (523, 361), (513, 365), (509, 373), (505, 357)]

def word240_7_639 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (541, 2), (529, 519), (533, 523)]

def word240_7_640 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_639 word240_2_195

def word240_7_641 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word240_2_408, 240, 10)) (some 154) ([2, 4, 6]) (some (2, word240_7_640, 240, 11))

def word240_7_642 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 533), (559, 529), (553, 533)]

def word240_7_643 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (573, 2), (565, 559)]

def word240_7_644 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_643 word240_2_195

def word240_7_645 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word240_2_438, 240, 12)) (some 70) ([2]) (some (2, word240_7_644, 240, 13))

def word240_7_646 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_464 word240_2_468

def word240_7_647 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_646

def word240_7_648 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_645 word240_7_647

def word240_7_649 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_642 word240_7_648

def word240_7_650 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_649

def word240_7_651 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_641 word240_7_650

def word240_7_652 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_638 word240_7_651

def word240_7_653 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_652

def word240_7_654 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_637 word240_7_653

def word240_7_655 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_316 word240_7_654

def word240_7_656 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_655

def word240_7_657 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_313 word240_7_656

def word240_7_658 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_657

def word240_7_659 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_611 word240_7_658

def word240_7_660 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_608 word240_7_659

def word240_7_661 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_283 word240_7_660

def word240_7_662 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_279 word240_7_661

def word240_7_663 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_276 word240_7_662

def word240_7_664 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_275 word240_7_663

def word240_7_665 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_664

def word240_7_666 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_607 word240_7_665

def word240_7_667 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_604 word240_7_666

def word240_7_668 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_667

def word240_7_669 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_603 word240_7_668

def word240_7_670 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_599 word240_7_669

def word240_7_671 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_211 word240_7_670

def word240_7_672 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_7_671

def word240_7_673 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_598 word240_7_672

def word240_7_674 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_594 word240_7_673

def pass240_7 : WordLangProgHOL (BitVec 64) :=
word240_7_674
theorem pass240_7_eq : WordUnreach.removeUnreach (pass240_6) = pass240_7 := by
  kernel_rfl
#print axioms pass240_7_eq
end InitECandidate.Proofs.WordStages
