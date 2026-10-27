import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass79_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word79_5_527 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1521, 1457)]

def word79_5_528 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_900 word79_5_527

def word79_5_529 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_899 word79_5_528

def word79_5_531 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_529 word79_2_904

def word79_5_532 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_524 word79_5_531

def word79_5_535 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1537, 1473)]

def word79_5_536 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_908 word79_5_535

def word79_5_537 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_907 word79_5_536

def word79_5_539 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_537 word79_2_912

def word79_5_540 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_532 word79_5_539

def word79_5_548 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_540 word79_3_547

def word79_5_549 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_548 word79_0_6

def word79_5_552 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1585, 1521)]

def word79_5_553 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_939 word79_5_552

def word79_5_554 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_938 word79_5_553

def word79_5_556 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_554 word79_2_943

def word79_5_557 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_549 word79_5_556

def word79_5_560 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1601, 1537)]

def word79_5_561 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_947 word79_5_560

def word79_5_562 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_946 word79_5_561

def word79_5_564 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_562 word79_2_951

def word79_5_565 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_557 word79_5_564

def word79_5_573 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_565 word79_3_572

def word79_5_574 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_573 word79_0_6

def word79_5_578 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_574 word79_4_577

def word79_5_580 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_578 word79_2_981

def word79_5_584 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_580 word79_2_985

def word79_5_585 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1677, 1349), (1669, 1353), (1665, 1357)]

def word79_5_586 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_584 word79_5_585

def word79_5_591 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_590 word79_5_585

def word79_5_592 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1365 (Flapjack.WordRegImm.reg 1373) word79_5_586 word79_5_591

def word79_5_593 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_811 word79_5_592

def word79_5_594 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_593 word79_0_6

def word79_5_595 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1349, 1677), (1353, 1669), (1357, 1665), (1361, 1361)]

def word79_5_596 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_594 word79_5_595

def word79_5_597 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word79_5_596 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word79_5_598 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_805 word79_5_597

def word79_5_599 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_467 word79_5_598

def word79_5_600 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_599 word79_0_6

def word79_5_601 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_600 word79_0_6

def word79_5_643 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1837, 1701), (1829, 1705), (1825, 1709)]

def word79_5_644 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_643 word79_5_643

def word79_5_648 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_648 word79_5_643

def word79_5_649 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1717 (Flapjack.WordRegImm.reg 1725) word79_5_644 word79_5_648

def word79_5_650 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1025 word79_5_649

def word79_5_651 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_650 word79_0_6

def word79_5_652 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1701, 1837), (1705, 1829), (1709, 1825), (1713, 1713)]

def word79_5_653 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_651 word79_5_652

def word79_5_654 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word79_5_653 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word79_5_655 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1019 word79_5_654

def word79_5_656 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_601 word79_5_655

def word79_5_657 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_656 word79_0_6

def word79_5_659 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_657 word79_2_1113

def word79_5_662 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 57 (Flapjack.WordRegImm.reg 61) word79_5_659 word79_3_663

def word79_5_663 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_11 word79_5_662

def word79_5_664 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_663 word79_0_6

def word79_5_665 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_664 word79_0_6

def word79_5_737 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2105, 2025)]

def word79_5_738 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1254 word79_5_737

def word79_5_739 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1253 word79_5_738

def word79_5_741 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_739 word79_2_1258

def word79_5_742 : WordLangProgHOL (BitVec 64) :=
.seq word79_4_736 word79_5_741

def word79_5_744 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_742 word79_2_1261

def word79_5_747 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2125, 2045)]

def word79_5_748 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1264 word79_5_747

def word79_5_749 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1263 word79_5_748

def word79_5_751 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_749 word79_2_1268

def word79_5_752 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_744 word79_5_751

def word79_5_754 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_752 word79_2_1271

def word79_5_756 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_754 word79_2_1273

def word79_5_758 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_756 word79_2_1275

def word79_5_766 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_758 word79_3_767

def word79_5_767 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_766 word79_0_6

def word79_5_770 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2185, 2105)]

def word79_5_771 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1301 word79_5_770

def word79_5_772 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1300 word79_5_771

def word79_5_774 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_772 word79_2_1305

def word79_5_775 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_767 word79_5_774

def word79_5_777 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_775 word79_2_1308

def word79_5_780 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2205, 2125)]

def word79_5_781 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1311 word79_5_780

def word79_5_782 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1310 word79_5_781

def word79_5_784 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_782 word79_2_1315

def word79_5_785 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_777 word79_5_784

def word79_5_787 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_785 word79_2_1318

def word79_5_789 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_787 word79_2_1320

def word79_5_791 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_789 word79_2_1322

def word79_5_799 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_791 word79_3_800

def word79_5_800 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_799 word79_0_6

def word79_5_803 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2265, 2185)]

def word79_5_804 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1348 word79_5_803

def word79_5_805 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1347 word79_5_804

def word79_5_807 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_805 word79_2_1352

def word79_5_808 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_800 word79_5_807

def word79_5_810 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_808 word79_2_1355

def word79_5_813 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2285, 2205)]

def word79_5_814 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1358 word79_5_813

def word79_5_815 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1357 word79_5_814

def word79_5_817 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_815 word79_2_1362

def word79_5_818 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_810 word79_5_817

def word79_5_820 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_818 word79_2_1365

def word79_5_822 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_820 word79_2_1367

def word79_5_824 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_822 word79_2_1369

def word79_5_832 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_824 word79_3_833

def word79_5_833 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_832 word79_0_6

def word79_5_836 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2345, 2265)]

def word79_5_837 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1395 word79_5_836

def word79_5_838 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1394 word79_5_837

def word79_5_840 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_838 word79_2_1399

def word79_5_841 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_833 word79_5_840

def word79_5_843 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_841 word79_2_1402

def word79_5_846 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2365, 2285)]

def word79_5_847 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1405 word79_5_846

def word79_5_848 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1404 word79_5_847

def word79_5_850 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_848 word79_2_1409

def word79_5_851 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_843 word79_5_850

def word79_5_853 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_851 word79_2_1412

def word79_5_855 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_853 word79_2_1414

def word79_5_857 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_855 word79_2_1416

def word79_5_865 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_857 word79_3_866

def word79_5_866 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_865 word79_0_6

def word79_5_869 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2425, 2345)]

def word79_5_870 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1442 word79_5_869

def word79_5_871 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1441 word79_5_870

def word79_5_873 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_871 word79_2_1446

def word79_5_874 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_866 word79_5_873

def word79_5_876 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_874 word79_2_1449

def word79_5_879 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2445, 2365)]

def word79_5_880 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1452 word79_5_879

def word79_5_881 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1451 word79_5_880

def word79_5_883 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_881 word79_2_1456

def word79_5_884 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_876 word79_5_883

def word79_5_886 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_884 word79_2_1459

def word79_5_888 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_886 word79_2_1461

def word79_5_890 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_888 word79_2_1463

def word79_5_898 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_890 word79_3_899

def word79_5_899 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_898 word79_0_6

def word79_5_902 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2505, 2425)]

def word79_5_903 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1489 word79_5_902

def word79_5_904 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1488 word79_5_903

def word79_5_906 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_904 word79_2_1493

def word79_5_907 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_899 word79_5_906

def word79_5_909 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_907 word79_2_1496

def word79_5_912 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2525, 2445)]

def word79_5_913 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1499 word79_5_912

def word79_5_914 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1498 word79_5_913

def word79_5_916 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_914 word79_2_1503

def word79_5_917 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_909 word79_5_916

def word79_5_919 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_917 word79_2_1506

def word79_5_921 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_919 word79_2_1508

def word79_5_923 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_921 word79_2_1510

def word79_5_931 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_923 word79_3_932

def word79_5_932 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_931 word79_0_6

def word79_5_936 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_932 word79_4_937

def word79_5_938 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_936 word79_2_1539

def word79_5_941 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_938 word79_2_1542

def word79_5_942 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2609, 1909), (2605, 1913), (2601, 1917)]

def word79_5_943 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_941 word79_5_942

def word79_5_947 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_948 word79_5_942

def word79_5_948 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1925 (Flapjack.WordRegImm.reg 1933) word79_5_943 word79_5_947

def word79_5_949 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1153 word79_5_948

def word79_5_950 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_949 word79_0_6

def word79_5_951 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1909, 2609), (1913, 2605), (1917, 2601), (1921, 1921)]

def word79_5_952 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_950 word79_5_951

def word79_5_953 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word79_5_952 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word79_5_954 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1147 word79_5_953

def word79_5_955 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_665 word79_5_954

def word79_5_956 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_955 word79_0_6

def word79_5_957 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_956 word79_0_6

def word79_5_1001 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2777, 2641), (2773, 2645), (2769, 2649)]

def word79_5_1002 : WordLangProgHOL (BitVec 64) :=
.seq word79_3_1003 word79_5_1001

def word79_5_1006 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 2657 (Flapjack.WordRegImm.reg 2661) word79_5_1002 word79_3_1008

def word79_5_1007 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1587 word79_5_1006

def word79_5_1008 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_1007 word79_0_6

def word79_5_1010 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_1008 word79_2_1683

def word79_5_1011 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          Flapjack.Spt.ln)))
    Flapjack.Spt.ln)) word79_5_1010 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)))
        Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    Flapjack.Spt.ln))

def word79_5_1012 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1583 word79_5_1011

def word79_5_1013 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_957 word79_5_1012

def word79_5_1014 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_1013 word79_0_6

def word79_5_1016 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_1014 word79_2_1689

def word79_5_1019 : WordLangProgHOL (BitVec 64) :=
.seq word79_5_1016 word79_2_1692

def word79_5_1020 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_0 word79_5_1019

def pass79_5 : WordLangProgHOL (BitVec 64) :=
word79_5_1020
theorem pass79_5_eq : WordCopy.copyProp (pass79_4) = pass79_5 := by
  kernel_rfl
#print axioms pass79_5_eq
end InitECandidate.Proofs.WordStages
