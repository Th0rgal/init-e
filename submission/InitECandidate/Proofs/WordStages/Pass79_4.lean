import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass79_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word79_4_502 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1457, 1393)]

def word79_4_503 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_861 word79_4_502

def word79_4_504 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_860 word79_4_503

def word79_4_506 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_504 word79_2_865

def word79_4_507 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_499 word79_4_506

def word79_4_510 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1473, 1409)]

def word79_4_511 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_869 word79_4_510

def word79_4_512 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_868 word79_4_511

def word79_4_514 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_512 word79_2_873

def word79_4_515 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_507 word79_4_514

def word79_4_523 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_515 word79_3_522

def word79_4_524 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_523 word79_0_6

def word79_4_527 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1521, 1393)]

def word79_4_528 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_900 word79_4_527

def word79_4_529 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_899 word79_4_528

def word79_4_531 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_529 word79_2_904

def word79_4_532 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_524 word79_4_531

def word79_4_535 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1537, 1409)]

def word79_4_536 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_908 word79_4_535

def word79_4_537 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_907 word79_4_536

def word79_4_539 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_537 word79_2_912

def word79_4_540 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_532 word79_4_539

def word79_4_548 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_540 word79_3_547

def word79_4_549 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_548 word79_0_6

def word79_4_552 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1585, 1393)]

def word79_4_553 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_939 word79_4_552

def word79_4_554 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_938 word79_4_553

def word79_4_556 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_554 word79_2_943

def word79_4_557 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_549 word79_4_556

def word79_4_560 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1601, 1409)]

def word79_4_561 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_947 word79_4_560

def word79_4_562 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_946 word79_4_561

def word79_4_564 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_562 word79_2_951

def word79_4_565 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_557 word79_4_564

def word79_4_573 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_565 word79_3_572

def word79_4_574 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_573 word79_0_6

def word79_4_576 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1645, 1373)]

def word79_4_577 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_977 word79_4_576

def word79_4_578 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_574 word79_4_577

def word79_4_580 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_578 word79_2_981

def word79_4_584 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_580 word79_2_985

def word79_4_586 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_584 word79_3_585

def word79_4_593 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1365 (Flapjack.WordRegImm.reg 1373) word79_4_586 word79_3_592

def word79_4_594 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_811 word79_4_593

def word79_4_595 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_594 word79_0_6

def word79_4_597 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_595 word79_2_1012

def word79_4_598 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln)))))
    Flapjack.Spt.ln)) word79_4_597 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
              Flapjack.Spt.ln)))))
    Flapjack.Spt.ln))

def word79_4_599 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_805 word79_4_598

def word79_4_600 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_467 word79_4_599

def word79_4_601 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_600 word79_0_6

def word79_4_602 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_601 word79_0_6

def word79_4_636 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1805, 1725)]

def word79_4_637 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1074 word79_4_636

def word79_4_638 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_634 word79_4_637

def word79_4_640 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_638 word79_2_1078

def word79_4_643 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_640 word79_2_1081

def word79_4_645 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_643 word79_3_644

def word79_4_651 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1717 (Flapjack.WordRegImm.reg 1725) word79_4_645 word79_3_650

def word79_4_652 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1025 word79_4_651

def word79_4_653 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_652 word79_0_6

def word79_4_655 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_653 word79_2_1107

def word79_4_656 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))))
    Flapjack.Spt.ln)) word79_4_655 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))))
    Flapjack.Spt.ln))

def word79_4_657 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1019 word79_4_656

def word79_4_658 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_602 word79_4_657

def word79_4_659 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_658 word79_0_6

def word79_4_661 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_659 word79_2_1113

def word79_4_664 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 57 (Flapjack.WordRegImm.reg 61) word79_4_661 word79_3_663

def word79_4_665 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_11 word79_4_664

def word79_4_666 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_665 word79_0_6

def word79_4_667 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_666 word79_0_6

def word79_4_706 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2025, 1953)]

def word79_4_707 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1207 word79_4_706

def word79_4_708 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1206 word79_4_707

def word79_4_710 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_708 word79_2_1211

def word79_4_711 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_703 word79_4_710

def word79_4_713 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_711 word79_2_1214

def word79_4_716 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2045, 1969)]

def word79_4_717 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1217 word79_4_716

def word79_4_718 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1216 word79_4_717

def word79_4_720 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_718 word79_2_1221

def word79_4_721 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_713 word79_4_720

def word79_4_723 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_721 word79_2_1224

def word79_4_725 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_723 word79_2_1226

def word79_4_727 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_725 word79_2_1228

def word79_4_735 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_727 word79_3_734

def word79_4_736 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_735 word79_0_6

def word79_4_739 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2105, 1953)]

def word79_4_740 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1254 word79_4_739

def word79_4_741 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1253 word79_4_740

def word79_4_743 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_741 word79_2_1258

def word79_4_744 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_736 word79_4_743

def word79_4_746 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_744 word79_2_1261

def word79_4_749 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2125, 1969)]

def word79_4_750 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1264 word79_4_749

def word79_4_751 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1263 word79_4_750

def word79_4_753 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_751 word79_2_1268

def word79_4_754 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_746 word79_4_753

def word79_4_756 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_754 word79_2_1271

def word79_4_758 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_756 word79_2_1273

def word79_4_760 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_758 word79_2_1275

def word79_4_768 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_760 word79_3_767

def word79_4_769 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_768 word79_0_6

def word79_4_772 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2185, 1953)]

def word79_4_773 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1301 word79_4_772

def word79_4_774 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1300 word79_4_773

def word79_4_776 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_774 word79_2_1305

def word79_4_777 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_769 word79_4_776

def word79_4_779 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_777 word79_2_1308

def word79_4_782 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2205, 1969)]

def word79_4_783 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1311 word79_4_782

def word79_4_784 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1310 word79_4_783

def word79_4_786 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_784 word79_2_1315

def word79_4_787 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_779 word79_4_786

def word79_4_789 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_787 word79_2_1318

def word79_4_791 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_789 word79_2_1320

def word79_4_793 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_791 word79_2_1322

def word79_4_801 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_793 word79_3_800

def word79_4_802 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_801 word79_0_6

def word79_4_805 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2265, 1953)]

def word79_4_806 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1348 word79_4_805

def word79_4_807 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1347 word79_4_806

def word79_4_809 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_807 word79_2_1352

def word79_4_810 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_802 word79_4_809

def word79_4_812 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_810 word79_2_1355

def word79_4_815 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2285, 1969)]

def word79_4_816 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1358 word79_4_815

def word79_4_817 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1357 word79_4_816

def word79_4_819 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_817 word79_2_1362

def word79_4_820 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_812 word79_4_819

def word79_4_822 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_820 word79_2_1365

def word79_4_824 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_822 word79_2_1367

def word79_4_826 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_824 word79_2_1369

def word79_4_834 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_826 word79_3_833

def word79_4_835 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_834 word79_0_6

def word79_4_838 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2345, 1953)]

def word79_4_839 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1395 word79_4_838

def word79_4_840 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1394 word79_4_839

def word79_4_842 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_840 word79_2_1399

def word79_4_843 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_835 word79_4_842

def word79_4_845 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_843 word79_2_1402

def word79_4_848 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2365, 1969)]

def word79_4_849 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1405 word79_4_848

def word79_4_850 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1404 word79_4_849

def word79_4_852 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_850 word79_2_1409

def word79_4_853 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_845 word79_4_852

def word79_4_855 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_853 word79_2_1412

def word79_4_857 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_855 word79_2_1414

def word79_4_859 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_857 word79_2_1416

def word79_4_867 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_859 word79_3_866

def word79_4_868 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_867 word79_0_6

def word79_4_871 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2425, 1953)]

def word79_4_872 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1442 word79_4_871

def word79_4_873 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1441 word79_4_872

def word79_4_875 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_873 word79_2_1446

def word79_4_876 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_868 word79_4_875

def word79_4_878 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_876 word79_2_1449

def word79_4_881 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2445, 1969)]

def word79_4_882 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1452 word79_4_881

def word79_4_883 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1451 word79_4_882

def word79_4_885 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_883 word79_2_1456

def word79_4_886 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_878 word79_4_885

def word79_4_888 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_886 word79_2_1459

def word79_4_890 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_888 word79_2_1461

def word79_4_892 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_890 word79_2_1463

def word79_4_900 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_892 word79_3_899

def word79_4_901 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_900 word79_0_6

def word79_4_904 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2505, 1953)]

def word79_4_905 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1489 word79_4_904

def word79_4_906 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1488 word79_4_905

def word79_4_908 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_906 word79_2_1493

def word79_4_909 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_901 word79_4_908

def word79_4_911 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_909 word79_2_1496

def word79_4_914 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2525, 1969)]

def word79_4_915 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1499 word79_4_914

def word79_4_916 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1498 word79_4_915

def word79_4_918 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_916 word79_2_1503

def word79_4_919 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_911 word79_4_918

def word79_4_921 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_919 word79_2_1506

def word79_4_923 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_921 word79_2_1508

def word79_4_925 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_923 word79_2_1510

def word79_4_933 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_925 word79_3_932

def word79_4_934 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_933 word79_0_6

def word79_4_936 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2581, 1933)]

def word79_4_937 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1535 word79_4_936

def word79_4_938 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_934 word79_4_937

def word79_4_940 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_938 word79_2_1539

def word79_4_943 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_940 word79_2_1542

def word79_4_945 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_943 word79_3_944

def word79_4_951 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1925 (Flapjack.WordRegImm.reg 1933) word79_4_945 word79_3_950

def word79_4_952 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1153 word79_4_951

def word79_4_953 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_952 word79_0_6

def word79_4_955 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_953 word79_2_1576

def word79_4_956 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                Flapjack.Spt.ln))))))
    Flapjack.Spt.ln)) word79_4_955 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                Flapjack.Spt.ln))))))
    Flapjack.Spt.ln))

def word79_4_957 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1147 word79_4_956

def word79_4_958 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_667 word79_4_957

def word79_4_959 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_958 word79_0_6

def word79_4_960 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_959 word79_0_6

def word79_4_1016 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_960 word79_3_1015

def word79_4_1017 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_1016 word79_0_6

def word79_4_1019 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_1017 word79_2_1689

def word79_4_1022 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_1019 word79_2_1692

def word79_4_1023 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_0 word79_4_1022

def pass79_4 : WordLangProgHOL (BitVec 64) :=
word79_4_1023
theorem pass79_4_eq : WordCse.wordCommonSubexpElim (pass79_3) = pass79_4 := by
  kernel_rfl
#print axioms pass79_4_eq
end InitECandidate.Proofs.WordStages
