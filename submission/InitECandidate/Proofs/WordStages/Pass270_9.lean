import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass270_8
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def proposed270 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.ls 2)) 0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 3))
              (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 3 (Flapjack.Spt.ls 1)))
            (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 2 (Flapjack.Spt.ls 2)) (Flapjack.Spt.ls 5)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 0))
              (Flapjack.Spt.bn (Flapjack.Spt.ls 3) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))
            (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 7)) 1
              (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 7 Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs
            (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 0 (Flapjack.Spt.ls 5))
              (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))))
            0 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 1) 0 (Flapjack.Spt.ls 1)) 2 (Flapjack.Spt.ls 6)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 1) (Flapjack.Spt.ls 6)) 3
              (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))))
            (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 4) 2 (Flapjack.Spt.ls 0))
              (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 1))))))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 23) Flapjack.Spt.ln) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls 22) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24)))))))
def word270_9_464 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4, 4), (2, 2), (0, 0)]

def word270_9_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (4, 4), (6, 6), (44, 0), (46, 4), (48, 2)]

def word270_9_466 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4, 4), (6, 2), (14, 44), (12, 46), (10, 48)]

def word270_9_467 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (14, 44), (12, 46), (10, 48)]

def word270_9_468 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_467 word270_2_178

def word270_9_469 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))))
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word270_9_466, 270, 2)) (some 269) ([2, 4, 6]) (some (2, word270_9_468, 270, 3))

def word270_9_470 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 0 8#64)

def word270_9_471 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4, 4)]

def word270_9_472 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 0 4#64)

def word270_9_473 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(0, 0)]

def word270_9_474 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 0)

def word270_9_475 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 3#64)

def word270_9_476 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2)]

def word270_9_477 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_476 word270_2_178

def word270_9_478 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_475 word270_9_477

def word270_9_479 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_474 word270_9_478

def word270_9_480 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_473 word270_9_479

def word270_9_481 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_472 word270_9_480

def word270_9_482 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_9_481

def word270_9_483 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 0 (Flapjack.WordRegImm.reg 4) word270_9_482 word270_0_6

def word270_9_484 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 0#64)

def word270_9_485 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 0 0#64)

def word270_9_486 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(14, 14), (2, 2), (4, 4), (12, 12), (0, 0), (10, 10), (6, 6)]

def word270_9_487 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4, 4), (0, 0)]

def word270_9_488 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6, 6), (0, 0)]

def word270_9_489 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 8 0 (Flapjack.WordRegImm.reg 6)))

def word270_9_490 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def word270_9_491 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 2), (8, 8)]

def word270_9_492 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 2 2 (Flapjack.WordRegImm.imm 8#64)))

def word270_9_493 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.or 2 8 (Flapjack.WordRegImm.reg 2)))

def word270_9_494 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(0, 0), (2, 2)]

def word270_9_495 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 0 0 (Flapjack.WordRegImm.imm 1#64)))

def word270_9_496 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (4, 4), (0, 0), (6, 6)]

def word270_9_497 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_496 word270_0_57

def word270_9_498 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_495 word270_9_497

def word270_9_499 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_494 word270_9_498

def word270_9_500 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_493 word270_9_499

def word270_9_501 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_492 word270_9_500

def word270_9_502 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_491 word270_9_501

def word270_9_503 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_490 word270_9_502

def word270_9_504 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_489 word270_9_503

def word270_9_505 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_488 word270_9_504

def word270_9_506 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_9_505

def word270_9_507 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 0 (Flapjack.WordRegImm.reg 4) word270_9_506 word270_3_349

def word270_9_508 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_9_496

def word270_9_509 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_507 word270_9_508

def word270_9_510 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_487 word270_9_509

def word270_9_511 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () (Flapjack.Spt.ls ())) ()
    (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () Flapjack.Spt.ln))
  () Flapjack.Spt.ln) word270_9_510 (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) () Flapjack.Spt.ln)
  Flapjack.Spt.ln)

def word270_9_512 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 2)]

def word270_9_513 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 14 [2]

def word270_9_514 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_512 word270_9_513

def word270_9_515 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_9_514

def word270_9_516 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_511 word270_9_515

def word270_9_517 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_486 word270_9_516

def word270_9_518 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_9_517

def word270_9_519 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_485 word270_9_518

def word270_9_520 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_484 word270_9_519

def word270_9_521 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_9_520

def word270_9_522 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_9_521

def word270_9_523 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_483 word270_9_522

def word270_9_524 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_471 word270_9_523

def word270_9_525 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_470 word270_9_524

def word270_9_526 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_9_525

def word270_9_527 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_469 word270_9_526

def word270_9_528 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_465 word270_9_527

def word270_9_529 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_102 word270_9_528

def word270_9_530 : WordLangProgHOL (BitVec 64) :=
.seq word270_9_464 word270_9_529

def pass270_9 : WordLangProgHOL (BitVec 64) :=
word270_9_530
theorem pass270_9_eq : WordToWord.wordAllocWith RegAlloc.regAllocExecutable 270 riscvConfig RiscVConfig.pancakeRiscVBackendConfig.wordToWordConf.regAlg (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) (pass270_8) proposed270 = pass270_9 := by
  kernel_rfl
#print axioms pass270_9_eq
end InitECandidate.Proofs.WordStages
