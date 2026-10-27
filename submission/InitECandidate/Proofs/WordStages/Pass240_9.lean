import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass240_8
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def proposed240 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4))) 0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 7))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 5) (Flapjack.Spt.ls 3)))
              (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 26 (Flapjack.Spt.ls 7))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 3))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 9) (Flapjack.Spt.ls 7)))
              (Flapjack.Spt.bs (Flapjack.Spt.ls 22) 27 (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 26 Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 2))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.bs Flapjack.Spt.ln 0 (Flapjack.Spt.ls 0))))
              (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 8))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1)) 1
                (Flapjack.Spt.bn (Flapjack.Spt.ls 2) Flapjack.Spt.ln))
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 8) Flapjack.Spt.ln) 23
                (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.ls 8))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 23)))
              (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 0 (Flapjack.Spt.ls 22)) 0
                (Flapjack.Spt.bn (Flapjack.Spt.ls 5) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 0) (Flapjack.Spt.ls 22)))
              (Flapjack.Spt.bs
                (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))) 24
                (Flapjack.Spt.bs (Flapjack.Spt.ls 8) 0 Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 8))
                (Flapjack.Spt.bn (Flapjack.Spt.ls 8) (Flapjack.Spt.ls 6)))
              (Flapjack.Spt.bn (Flapjack.Spt.ls 23)
                (Flapjack.Spt.bs (Flapjack.Spt.ls 2) 27 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 6)) (Flapjack.Spt.ls 3))
              (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 4) (Flapjack.Spt.ls 2)) 22 (Flapjack.Spt.ls 22))))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 27 (Flapjack.Spt.ls 24)) 27
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 26))))
            (Flapjack.Spt.bn (Flapjack.Spt.ls 22)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln 22 (Flapjack.Spt.ls 23))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 24 (Flapjack.Spt.ls 22)) 23
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 24))))
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 28)))
              (Flapjack.Spt.bn (Flapjack.Spt.ls 26) Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln 26 (Flapjack.Spt.ls 23)) 24
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 25))))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.ls 27)
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bs
              (Flapjack.Spt.bs Flapjack.Spt.ln 23
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22))))
              22 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 23))))
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 27)))
              (Flapjack.Spt.bn (Flapjack.Spt.ls 25) Flapjack.Spt.ln)))))))
def word240_9_750 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(44, 0), (46, 4), (48, 2), (54, 6)]

def word240_9_751 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(0, 2), (44, 44), (46, 46), (48, 48), (54, 54)]

def word240_9_752 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (44, 44), (46, 46), (48, 48), (54, 54)]

def word240_9_753 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_752 word240_2_195

def word240_9_754 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))))
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_9_751, 240, 2)) (some 69) ([]) (some (2, word240_9_753, 240, 3))

def word240_9_755 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 64#64)

def word240_9_756 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (44, 44), (46, 46), (48, 48), (52, 0), (54, 54)]

def word240_9_757 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(6, 2), (44, 44), (4, 46), (0, 48), (52, 52), (54, 54)]

def word240_9_758 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (44, 44), (4, 46), (0, 48), (52, 52), (54, 54)]

def word240_9_759 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_758 word240_2_195

def word240_9_760 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))))
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_9_757, 240, 4)) (some 68) ([2]) (some (2, word240_9_759, 240, 5))

def word240_9_761 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 0), (4, 4), (6, 6), (44, 44), (46, 4), (48, 0), (50, 6), (52, 52), (54, 54)]

def word240_9_762 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(44, 44), (46, 46), (48, 48), (0, 50), (52, 52), (54, 54)]

def word240_9_763 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (44, 44), (46, 46), (48, 48), (0, 50), (52, 52), (54, 54)]

def word240_9_764 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_763 word240_2_195

def word240_9_765 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))))
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_9_762, 240, 6)) (some 237) ([2, 4, 6]) (some (2, word240_9_764, 240, 7))

def word240_9_766 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(0, 0)]

def word240_9_767 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 2 0 (Flapjack.WordRegImm.imm 32#64)))

def word240_9_768 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 2)]

def word240_9_769 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 4 32#64)

def word240_9_770 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (4, 4), (44, 44), (46, 46), (48, 48), (50, 0), (52, 52), (54, 54), (56, 2)]

def word240_9_771 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(44, 44), (14, 46), (12, 48), (0, 50), (46, 52), (6, 54), (4, 56)]

def word240_9_772 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (44, 44), (14, 46), (12, 48), (0, 50), (46, 52), (6, 54), (4, 56)]

def word240_9_773 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_772 word240_2_195

def word240_9_774 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln))))
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_9_771, 240, 8)) (some 78) ([2, 4]) (some (2, word240_9_773, 240, 9))

def word240_9_775 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(44, 44), (14, 14), (12, 12), (2, 0), (46, 46), (6, 6), (16, 16), (4, 4)]

def word240_9_776 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(14, 14), (16, 16)]

def word240_9_777 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(16, 16)]

def word240_9_778 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 0 16 (Flapjack.WordRegImm.imm 3#64)))

def word240_9_779 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4, 4)]

def word240_9_780 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 0 0 (Flapjack.WordRegImm.reg 4)))

def word240_9_781 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 10 (Flapjack.WordLangAddr.addr 0 0#64))

def word240_9_782 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(0, 0), (4, 4), (16, 16)]

def word240_9_783 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 18 1#64)

def word240_9_784 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.and 8 16 (Flapjack.WordRegImm.imm 7#64)))

def word240_9_785 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(8, 8)]

def word240_9_786 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 8 18 (Flapjack.WordRegImm.reg 8)))

def word240_9_787 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(10, 10)]

def word240_9_788 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.or 8 8 (Flapjack.WordRegImm.reg 10)))

def word240_9_789 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 8 (Flapjack.WordLangAddr.addr 0 0#64))

def word240_9_790 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 16 16 (Flapjack.WordRegImm.imm 1#64)))

def word240_9_791 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(14, 14), (16, 16), (4, 4)]

def word240_9_792 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_791 word240_0_57

def word240_9_793 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_790 word240_9_792

def word240_9_794 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_777 word240_9_793

def word240_9_795 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_789 word240_9_794

def word240_9_796 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_788 word240_9_795

def word240_9_797 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_787 word240_9_796

def word240_9_798 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_786 word240_9_797

def word240_9_799 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_785 word240_9_798

def word240_9_800 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_784 word240_9_799

def word240_9_801 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_777 word240_9_800

def word240_9_802 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_783 word240_9_801

def word240_9_803 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_782 word240_9_802

def word240_9_804 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_781 word240_9_803

def word240_9_805 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_780 word240_9_804

def word240_9_806 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_779 word240_9_805

def word240_9_807 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_778 word240_9_806

def word240_9_808 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_777 word240_9_807

def word240_9_809 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_808

def word240_9_810 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 16 (Flapjack.WordRegImm.reg 14) word240_9_809 word240_3_514

def word240_9_811 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_791

def word240_9_812 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_810 word240_9_811

def word240_9_813 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_776 word240_9_812

def word240_9_814 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) () Flapjack.Spt.ln) ()
      Flapjack.Spt.ln)
    ()
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) () Flapjack.Spt.ln) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
  Flapjack.Spt.ln) word240_9_813 (Flapjack.Spt.bn
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln) ()
      Flapjack.Spt.ln)
    ()
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln) ()
      Flapjack.Spt.ln))
  Flapjack.Spt.ln)

def word240_9_815 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (4, 4), (6, 6), (44, 44), (46, 46)]

def word240_9_816 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(44, 44), (0, 46)]

def word240_9_817 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (44, 44), (0, 46)]

def word240_9_818 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_817 word240_2_195

def word240_9_819 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_9_816, 240, 10)) (some 154) ([2, 4, 6]) (some (2, word240_9_818, 240, 11))

def word240_9_820 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 0), (44, 44)]

def word240_9_821 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(0, 44)]

def word240_9_822 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (0, 44)]

def word240_9_823 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_822 word240_2_195

def word240_9_824 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_9_821, 240, 12)) (some 70) ([2]) (some (2, word240_9_823, 240, 13))

def word240_9_825 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 0#64)

def word240_9_826 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [2]

def word240_9_827 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_768 word240_9_826

def word240_9_828 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_825 word240_9_827

def word240_9_829 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_828

def word240_9_830 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_824 word240_9_829

def word240_9_831 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_820 word240_9_830

def word240_9_832 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_831

def word240_9_833 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_819 word240_9_832

def word240_9_834 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_815 word240_9_833

def word240_9_835 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_834

def word240_9_836 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_814 word240_9_835

def word240_9_837 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_775 word240_9_836

def word240_9_838 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_837

def word240_9_839 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_155 word240_9_838

def word240_9_840 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_839

def word240_9_841 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_774 word240_9_840

def word240_9_842 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_770 word240_9_841

def word240_9_843 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_769 word240_9_842

def word240_9_844 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_768 word240_9_843

def word240_9_845 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_767 word240_9_844

def word240_9_846 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_766 word240_9_845

def word240_9_847 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_846

def word240_9_848 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_765 word240_9_847

def word240_9_849 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_761 word240_9_848

def word240_9_850 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_849

def word240_9_851 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_760 word240_9_850

def word240_9_852 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_756 word240_9_851

def word240_9_853 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_755 word240_9_852

def word240_9_854 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_3 word240_9_853

def word240_9_855 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_754 word240_9_854

def word240_9_856 : WordLangProgHOL (BitVec 64) :=
.seq word240_9_750 word240_9_855

def pass240_9 : WordLangProgHOL (BitVec 64) :=
word240_9_856
theorem pass240_9_eq : WordToWord.wordAllocWith RegAlloc.regAllocExecutable 240 riscvConfig RiscVConfig.pancakeRiscVBackendConfig.wordToWordConf.regAlg (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) (pass240_8) proposed240 = pass240_9 := by
  kernel_rfl
#print axioms pass240_9_eq
end InitECandidate.Proofs.WordStages
