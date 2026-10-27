import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass79_7
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word79_8_440 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1457, 1393), (1453, 1389)]

def word79_8_442 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1473, 1409), (1469, 1405)]

def word79_8_450 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1521, 1457), (1517, 1453)]

def word79_8_452 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1537, 1473), (1533, 1469)]

def word79_8_460 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1585, 1521), (1581, 1517)]

def word79_8_462 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1601, 1537), (1597, 1533)]

def word79_8_470 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1349, 1597), (1353, 1581), (1357, 1373), (1361, 1365)]

def word79_8_472 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_470 word79_0_211

def word79_8_473 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_472

def word79_8_474 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_473

def word79_8_475 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_469 word79_8_474

def word79_8_476 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_951 word79_8_475

def word79_8_477 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_462 word79_8_476

def word79_8_478 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_943 word79_8_477

def word79_8_479 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_460 word79_8_478

def word79_8_480 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_479

def word79_8_481 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_480

def word79_8_482 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_459 word79_8_481

def word79_8_483 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_912 word79_8_482

def word79_8_484 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_452 word79_8_483

def word79_8_485 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_904 word79_8_484

def word79_8_486 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_450 word79_8_485

def word79_8_487 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_486

def word79_8_488 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_487

def word79_8_489 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_449 word79_8_488

def word79_8_490 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_873 word79_8_489

def word79_8_491 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_442 word79_8_490

def word79_8_492 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_865 word79_8_491

def word79_8_493 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_440 word79_8_492

def word79_8_494 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_493

def word79_8_495 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_494

def word79_8_496 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_439 word79_8_495

def word79_8_497 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_829 word79_8_496

def word79_8_498 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_826 word79_8_497

def word79_8_499 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_430 word79_8_498

def word79_8_500 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_821 word79_8_499

def word79_8_501 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_818 word79_8_500

def word79_8_502 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_427 word79_8_501

def word79_8_503 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_502

def word79_8_508 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1365 (Flapjack.WordRegImm.reg 1373) word79_8_503 word79_3_590

def word79_8_511 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_508 word79_7_510

def word79_8_512 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_809 word79_8_511

def word79_8_513 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_425 word79_8_512

def word79_8_514 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word79_8_513 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word79_8_531 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1701, 1757), (1705, 1741), (1709, 1725), (1713, 1717)]

def word79_8_532 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_531 word79_0_211

def word79_8_533 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_532

def word79_8_534 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_533

def word79_8_535 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_530 word79_8_534

def word79_8_536 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1043 word79_8_535

def word79_8_537 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1040 word79_8_536

def word79_8_538 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_521 word79_8_537

def word79_8_539 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1035 word79_8_538

def word79_8_540 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1032 word79_8_539

def word79_8_541 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_518 word79_8_540

def word79_8_542 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_541

def word79_8_546 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1717 (Flapjack.WordRegImm.reg 1725) word79_8_542 word79_3_648

def word79_8_549 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_546 word79_7_548

def word79_8_550 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1023 word79_8_549

def word79_8_551 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_516 word79_8_550

def word79_8_552 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word79_8_551 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word79_8_555 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_552 word79_7_554

def word79_8_556 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1019 word79_8_555

def word79_8_557 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_556

def word79_8_558 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_557

def word79_8_559 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_514 word79_8_558

def word79_8_560 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_805 word79_8_559

def word79_8_561 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_560

def word79_8_562 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_561

def word79_8_563 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_562

def word79_8_564 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_423 word79_8_563

def word79_8_565 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_437 word79_8_564

def word79_8_566 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_435 word79_8_565

def word79_8_567 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_566

def word79_8_568 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_567

def word79_8_569 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_220 word79_8_568

def word79_8_570 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_286 word79_8_569

def word79_8_571 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_284 word79_8_570

def word79_8_572 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_571

def word79_8_573 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_572

def word79_8_574 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_143 word79_8_573

def word79_8_575 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_19 word79_8_574

def word79_8_576 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_17 word79_8_575

def word79_8_577 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_576

def word79_8_580 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 57 (Flapjack.WordRegImm.reg 61) word79_8_577 word79_3_663

def word79_8_598 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2025, 1953), (2021, 1949)]

def word79_8_601 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2045, 1969), (2041, 1965)]

def word79_8_611 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2105, 2025), (2101, 2021)]

def word79_8_614 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2125, 2045), (2121, 2041)]

def word79_8_624 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2185, 2105), (2181, 2101)]

def word79_8_627 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2205, 2125), (2201, 2121)]

def word79_8_637 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2265, 2185), (2261, 2181)]

def word79_8_640 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2285, 2205), (2281, 2201)]

def word79_8_650 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2345, 2265), (2341, 2261)]

def word79_8_653 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2365, 2285), (2361, 2281)]

def word79_8_663 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2425, 2345), (2421, 2341)]

def word79_8_666 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2445, 2365), (2441, 2361)]

def word79_8_676 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2505, 2425), (2501, 2421)]

def word79_8_679 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2525, 2445), (2521, 2441)]

def word79_8_689 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1909, 2521), (1913, 2501), (1917, 1933), (1921, 1925)]

def word79_8_690 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_689 word79_0_211

def word79_8_691 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_690

def word79_8_692 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_691

def word79_8_693 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_688 word79_8_692

def word79_8_694 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_682 word79_8_693

def word79_8_695 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1506 word79_8_694

def word79_8_696 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1503 word79_8_695

def word79_8_697 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_679 word79_8_696

def word79_8_698 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1496 word79_8_697

def word79_8_699 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1493 word79_8_698

def word79_8_700 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_676 word79_8_699

def word79_8_701 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_700

def word79_8_702 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_701

def word79_8_703 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_675 word79_8_702

def word79_8_704 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_669 word79_8_703

def word79_8_705 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1459 word79_8_704

def word79_8_706 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1456 word79_8_705

def word79_8_707 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_666 word79_8_706

def word79_8_708 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1449 word79_8_707

def word79_8_709 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1446 word79_8_708

def word79_8_710 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_663 word79_8_709

def word79_8_711 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_710

def word79_8_712 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_711

def word79_8_713 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_662 word79_8_712

def word79_8_714 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_656 word79_8_713

def word79_8_715 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1412 word79_8_714

def word79_8_716 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1409 word79_8_715

def word79_8_717 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_653 word79_8_716

def word79_8_718 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1402 word79_8_717

def word79_8_719 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1399 word79_8_718

def word79_8_720 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_650 word79_8_719

def word79_8_721 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_720

def word79_8_722 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_721

def word79_8_723 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_649 word79_8_722

def word79_8_724 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_643 word79_8_723

def word79_8_725 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1365 word79_8_724

def word79_8_726 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1362 word79_8_725

def word79_8_727 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_640 word79_8_726

def word79_8_728 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1355 word79_8_727

def word79_8_729 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1352 word79_8_728

def word79_8_730 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_637 word79_8_729

def word79_8_731 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_730

def word79_8_732 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_731

def word79_8_733 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_636 word79_8_732

def word79_8_734 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_630 word79_8_733

def word79_8_735 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1318 word79_8_734

def word79_8_736 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1315 word79_8_735

def word79_8_737 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_627 word79_8_736

def word79_8_738 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1308 word79_8_737

def word79_8_739 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1305 word79_8_738

def word79_8_740 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_624 word79_8_739

def word79_8_741 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_740

def word79_8_742 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_741

def word79_8_743 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_623 word79_8_742

def word79_8_744 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_617 word79_8_743

def word79_8_745 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1271 word79_8_744

def word79_8_746 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1268 word79_8_745

def word79_8_747 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_614 word79_8_746

def word79_8_748 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1261 word79_8_747

def word79_8_749 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1258 word79_8_748

def word79_8_750 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_611 word79_8_749

def word79_8_751 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_750

def word79_8_752 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_751

def word79_8_753 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_610 word79_8_752

def word79_8_754 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_604 word79_8_753

def word79_8_755 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1224 word79_8_754

def word79_8_756 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1221 word79_8_755

def word79_8_757 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_601 word79_8_756

def word79_8_758 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1214 word79_8_757

def word79_8_759 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1211 word79_8_758

def word79_8_760 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_598 word79_8_759

def word79_8_761 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_760

def word79_8_762 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_761

def word79_8_763 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_597 word79_8_762

def word79_8_764 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_590 word79_8_763

def word79_8_765 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1172 word79_8_764

def word79_8_766 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1168 word79_8_765

def word79_8_767 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_587 word79_8_766

def word79_8_768 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1164 word79_8_767

def word79_8_769 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1160 word79_8_768

def word79_8_770 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_584 word79_8_769

def word79_8_771 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_770

def word79_8_775 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1925 (Flapjack.WordRegImm.reg 1933) word79_8_771 word79_3_948

def word79_8_778 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_775 word79_7_777

def word79_8_779 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1151 word79_8_778

def word79_8_780 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_582 word79_8_779

def word79_8_781 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word79_8_780 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word79_8_800 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2641, 2693), (2645, 2677), (2649, 2749), (2653, 2661)]

def word79_8_801 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_800 word79_0_211

def word79_8_802 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1641 word79_8_801

def word79_8_803 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1640 word79_8_802

def word79_8_804 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_803

def word79_8_805 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_804

def word79_8_806 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_797 word79_8_805

def word79_8_807 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_790 word79_8_806

def word79_8_808 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1606 word79_8_807

def word79_8_809 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1602 word79_8_808

def word79_8_810 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_787 word79_8_809

def word79_8_811 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1598 word79_8_810

def word79_8_812 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1594 word79_8_811

def word79_8_813 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_784 word79_8_812

def word79_8_814 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_813

def word79_8_816 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 2657 (Flapjack.WordRegImm.reg 2661) word79_8_814 word79_3_1006

def word79_8_819 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_816 word79_7_818

def word79_8_820 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_783 word79_8_819

def word79_8_821 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word79_8_820 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word79_8_827 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_821 word79_7_826

def word79_8_828 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1583 word79_8_827

def word79_8_829 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_828

def word79_8_830 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_829

def word79_8_831 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_781 word79_8_830

def word79_8_832 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1147 word79_8_831

def word79_8_833 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_832

def word79_8_834 : WordLangProgHOL (BitVec 64) :=
.seq word79_0_6 word79_8_833

def word79_8_835 : WordLangProgHOL (BitVec 64) :=
.seq word79_8_580 word79_8_834

def word79_8_836 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_10 word79_8_835

def word79_8_837 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_7 word79_8_836

def word79_8_838 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_4 word79_8_837

def word79_8_839 : WordLangProgHOL (BitVec 64) :=
.seq word79_7_2 word79_8_838

def word79_8_840 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_1 word79_8_839

def word79_8_841 : WordLangProgHOL (BitVec 64) :=
.seq word79_2_0 word79_8_840

def pass79_8 : WordLangProgHOL (BitVec 64) :=
word79_8_841
theorem pass79_8_eq : WordAlloc.removeDeadProg (pass79_7) = pass79_8 := by
  kernel_rfl
#print axioms pass79_8_eq
end InitECandidate.Proofs.WordStages
