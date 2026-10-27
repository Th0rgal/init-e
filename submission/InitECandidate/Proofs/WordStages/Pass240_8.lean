import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass240_7
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word240_8_675 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(47, 0), (51, 4), (55, 2), (59, 6)]

def word240_8_676 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(89, 2), (65, 47), (69, 51), (73, 55), (77, 59)]

def word240_8_677 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (65, 47), (69, 51), (73, 55), (77, 59)]

def word240_8_678 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_677 word240_2_195

def word240_8_679 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word240_8_676, 240, 2)) (some 69) ([]) (some (2, word240_8_678, 240, 3))

def word240_8_680 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(161, 2), (129, 107), (133, 111), (137, 115), (141, 119), (145, 123)]

def word240_8_681 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (129, 107), (133, 111), (137, 115), (141, 119), (145, 123)]

def word240_8_682 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_681 word240_2_195

def word240_8_683 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
            (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word240_8_680, 240, 4)) (some 68) ([2]) (some (2, word240_8_682, 240, 5))

def word240_8_684 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2, 137), (4, 133), (6, 161), (179, 129), (183, 133), (187, 137), (191, 161), (195, 141), (199, 145)]

def word240_8_685 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (205, 179), (209, 183), (213, 187), (217, 191), (221, 195), (225, 199)]

def word240_8_686 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_685 word240_2_195

def word240_8_687 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word240_2_249, 240, 6)) (some 237) ([2, 4, 6]) (some (2, word240_8_686, 240, 7))

def word240_8_688 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2, 2), (297, 267), (301, 271), (305, 275), (309, 279), (313, 283), (317, 287), (321, 291)]

def word240_8_689 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_688 word240_2_195

def word240_8_690 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word240_2_286, 240, 8)) (some 78) ([2, 4]) (some (2, word240_8_689, 240, 9))

def word240_8_691 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(425, 405), (421, 401), (413, 393)]

def word240_8_692 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(349, 381), (369, 457), (373, 421)]

def word240_8_693 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_692 word240_0_57

def word240_8_694 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_360 word240_8_693

def word240_8_695 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_359 word240_8_694

def word240_8_696 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_357 word240_8_695

def word240_8_697 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_353 word240_8_696

def word240_8_698 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_352 word240_8_697

def word240_8_699 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_348 word240_8_698

def word240_8_700 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_347 word240_8_699

def word240_8_701 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_345 word240_8_700

def word240_8_702 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_344 word240_8_701

def word240_8_703 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_343 word240_8_702

def word240_8_704 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_691 word240_8_703

def word240_8_705 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_333 word240_8_704

def word240_8_706 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_329 word240_8_705

def word240_8_707 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_328 word240_8_706

def word240_8_708 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_326 word240_8_707

def word240_8_709 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_325 word240_8_708

def word240_8_710 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_8_709

def word240_8_711 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 377 (Flapjack.WordRegImm.reg 381) word240_8_710 word240_3_514

def word240_8_712 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_711 word240_7_634

def word240_8_713 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_612 word240_8_712

def word240_8_714 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word240_8_713 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word240_8_715 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 357), (4, 373), (6, 365), (519, 345), (523, 361)]

def word240_8_716 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (529, 519), (533, 523)]

def word240_8_717 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_716 word240_2_195

def word240_8_718 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word240_2_408, 240, 10)) (some 154) ([2, 4, 6]) (some (2, word240_8_717, 240, 11))

def word240_8_719 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 533), (559, 529)]

def word240_8_720 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (565, 559)]

def word240_8_721 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_720 word240_2_195

def word240_8_722 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word240_2_438, 240, 12)) (some 70) ([2]) (some (2, word240_8_721, 240, 13))

def word240_8_723 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_722 word240_7_647

def word240_8_724 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_719 word240_8_723

def word240_8_725 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_8_724

def word240_8_726 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_718 word240_8_725

def word240_8_727 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_715 word240_8_726

def word240_8_728 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_8_727

def word240_8_729 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_714 word240_8_728

def word240_8_730 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_316 word240_8_729

def word240_8_731 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_8_730

def word240_8_732 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_313 word240_8_731

def word240_8_733 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_8_732

def word240_8_734 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_690 word240_8_733

def word240_8_735 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_608 word240_8_734

def word240_8_736 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_283 word240_8_735

def word240_8_737 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_279 word240_8_736

def word240_8_738 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_276 word240_8_737

def word240_8_739 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_275 word240_8_738

def word240_8_740 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_8_739

def word240_8_741 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_687 word240_8_740

def word240_8_742 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_684 word240_8_741

def word240_8_743 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_8_742

def word240_8_744 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_683 word240_8_743

def word240_8_745 : WordLangProgHOL (BitVec 64) :=
.seq word240_7_599 word240_8_744

def word240_8_746 : WordLangProgHOL (BitVec 64) :=
.seq word240_2_211 word240_8_745

def word240_8_747 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_8_746

def word240_8_748 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_679 word240_8_747

def word240_8_749 : WordLangProgHOL (BitVec 64) :=
.seq word240_8_675 word240_8_748

def pass240_8 : WordLangProgHOL (BitVec 64) :=
word240_8_749
theorem pass240_8_eq : WordAlloc.removeDeadProg (pass240_7) = pass240_8 := by
  kernel_rfl
#print axioms pass240_8_eq
end InitECandidate.Proofs.WordStages
