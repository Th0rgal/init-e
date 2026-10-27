import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Source240
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word240_0_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def word240_0_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def word240_0_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () (Flapjack.Spt.ls ())) () Flapjack.Spt.ln, Flapjack.Spt.ln)), word240_0_0, 240, 2)) (some 69) ([]) (some (18, word240_0_1, 240, 3))

def word240_0_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def word240_0_4 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_2 word240_0_3

def word240_0_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 64#64)

def word240_0_6 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_4 word240_0_5

def word240_0_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def word240_0_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())) () (Flapjack.Spt.ls ())) ()
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_0_0, 240, 4)) (some 68) ([14]) (some (14, word240_0_7, 240, 5))

def word240_0_9 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_5 word240_0_8

def word240_0_10 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_6 word240_0_9

def word240_0_11 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_10 word240_0_3

def word240_0_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def word240_0_13 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_11 word240_0_12

def word240_0_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def word240_0_15 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_13 word240_0_14

def word240_0_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def word240_0_17 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_15 word240_0_16

def word240_0_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def word240_0_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.ls ()))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_0_0, 240, 6)) (some 237) ([22, 8, 16]) (some (22, word240_0_18, 240, 7))

def word240_0_20 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_17 word240_0_19

def word240_0_21 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_20 word240_0_3

def word240_0_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 32#64])

def word240_0_23 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_21 word240_0_22

def word240_0_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def word240_0_25 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_23 word240_0_24

def word240_0_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def word240_0_27 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_25 word240_0_26

def word240_0_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def word240_0_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())))
      () (Flapjack.Spt.ls ()))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_0_0, 240, 8)) (some 78) ([8, 16]) (some (8, word240_0_28, 240, 9))

def word240_0_30 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_26 word240_0_29

def word240_0_31 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_27 word240_0_30

def word240_0_32 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_31 word240_0_3

def word240_0_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def word240_0_34 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_32 word240_0_33

def word240_0_35 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_34 word240_0_3

def word240_0_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def word240_0_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def word240_0_38 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_36 word240_0_37

def word240_0_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def word240_0_40 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_39 word240_0_3

def word240_0_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def word240_0_42 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_40 word240_0_41

def word240_0_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 22)
        (Flapjack.WordLangExpHOL.const 3#64)])

def word240_0_44 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_42 word240_0_43

def word240_0_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def word240_0_46 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_44 word240_0_45

def word240_0_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 22)
        (Flapjack.WordLangExpHOL.const 3#64)])

def word240_0_48 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_46 word240_0_47

def word240_0_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 8,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.const 1#64)
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 7#64])])

def word240_0_50 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_48 word240_0_49

def word240_0_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 12 (Flapjack.WordLangAddr.addr 16 0#64))

def word240_0_52 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_50 word240_0_51

def word240_0_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 1#64])

def word240_0_54 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_52 word240_0_53

def word240_0_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def word240_0_56 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_54 word240_0_55

def word240_0_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def word240_0_58 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_56 word240_0_57

def word240_0_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def word240_0_60 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_59 word240_0_3

def word240_0_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def word240_0_62 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_60 word240_0_61

def word240_0_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def word240_0_64 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_62 word240_0_63

def word240_0_65 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 16 (Flapjack.WordRegImm.reg 12) word240_0_58 word240_0_64

def word240_0_66 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_38 word240_0_65

def word240_0_67 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_66 word240_0_3

def word240_0_68 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())) ()
      (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())))
    () (Flapjack.Spt.ls ()))
  () Flapjack.Spt.ln) word240_0_67 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())))
    Flapjack.Spt.ln)
  () Flapjack.Spt.ln)

def word240_0_69 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_35 word240_0_68

def word240_0_70 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_69 word240_0_3

def word240_0_71 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_70 word240_0_16

def word240_0_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def word240_0_73 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_71 word240_0_72

def word240_0_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def word240_0_75 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_73 word240_0_74

def word240_0_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def word240_0_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln) ()
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word240_0_0, 240, 10)) (some 154) ([16, 12, 20]) (some (16, word240_0_76, 240, 11))

def word240_0_78 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_75 word240_0_77

def word240_0_79 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_78 word240_0_3

def word240_0_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def word240_0_81 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_79 word240_0_80

def word240_0_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls (), Flapjack.Spt.ln)), word240_0_0, 240, 12)) (some 70) ([16]) (some (16, word240_0_76, 240, 13))

def word240_0_83 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_81 word240_0_82

def word240_0_84 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_83 word240_0_3

def word240_0_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def word240_0_86 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_84 word240_0_85

def word240_0_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def word240_0_88 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_86 word240_0_87

def pass240_0 : WordLangProgHOL (BitVec 64) :=
word240_0_88
theorem pass240_0_eq : WordSimp.compileExp (source240.2.2) = pass240_0 := by
  kernel_rfl
#print axioms pass240_0_eq
end InitECandidate.Proofs.WordStages
