import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Source276
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word276_0_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1024#64)

def word276_0_1 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_0 word276_0_0

def word276_0_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def word276_0_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def word276_0_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls ()) () Flapjack.Spt.ln, Flapjack.Spt.ln)), word276_0_2, 276, 2)) (some 68) ([18]) (some (18, word276_0_3, 276, 3))

def word276_0_5 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_1 word276_0_4

def word276_0_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def word276_0_7 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_5 word276_0_6

def word276_0_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 9#64])

def word276_0_9 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_7 word276_0_8

def word276_0_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def word276_0_11 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_9 word276_0_10

def word276_0_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def word276_0_13 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_11 word276_0_12

def word276_0_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 32#64)

def word276_0_15 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_13 word276_0_14

def word276_0_16 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_15 word276_0_14

def word276_0_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def word276_0_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 4)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 5))

def word276_0_19 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_16 word276_0_18

def word276_0_20 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_19 word276_0_6

def word276_0_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 6])

def word276_0_22 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_20 word276_0_21

def word276_0_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def word276_0_24 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_22 word276_0_23

def word276_0_25 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_24 word276_0_10

def word276_0_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def word276_0_27 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_25 word276_0_26

def word276_0_28 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_27 word276_0_14

def word276_0_29 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_28 word276_0_14

def word276_0_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 6)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 7))

def word276_0_31 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_29 word276_0_30

def word276_0_32 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_31 word276_0_6

def word276_0_33 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_32 word276_0_21

def word276_0_34 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_33 word276_0_23

def word276_0_35 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_34 word276_0_10

def word276_0_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def word276_0_37 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_35 word276_0_36

def word276_0_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 20#64)

def word276_0_39 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_37 word276_0_38

def word276_0_40 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_39 word276_0_38

def word276_0_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 8)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 9))

def word276_0_42 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_40 word276_0_41

def word276_0_43 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_42 word276_0_6

def word276_0_44 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_43 word276_0_21

def word276_0_45 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_44 word276_0_23

def word276_0_46 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_45 word276_0_10

def word276_0_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def word276_0_48 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_46 word276_0_47

def word276_0_49 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_48 word276_0_14

def word276_0_50 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_49 word276_0_14

def word276_0_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 10)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 11))

def word276_0_52 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_50 word276_0_51

def word276_0_53 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_52 word276_0_6

def word276_0_54 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_53 word276_0_21

def word276_0_55 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_54 word276_0_23

def word276_0_56 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_55 word276_0_10

def word276_0_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def word276_0_58 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_56 word276_0_57

def word276_0_59 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_58 word276_0_14

def word276_0_60 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_59 word276_0_14

def word276_0_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 12)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 13))

def word276_0_62 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_60 word276_0_61

def word276_0_63 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_62 word276_0_6

def word276_0_64 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_63 word276_0_21

def word276_0_65 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_64 word276_0_23

def word276_0_66 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_65 word276_0_10

def word276_0_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def word276_0_68 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_66 word276_0_67

def word276_0_69 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_68 word276_0_14

def word276_0_70 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_69 word276_0_14

def word276_0_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 14)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 15))

def word276_0_72 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_70 word276_0_71

def word276_0_73 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_72 word276_0_6

def word276_0_74 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_73 word276_0_21

def word276_0_75 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_74 word276_0_23

def word276_0_76 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_75 word276_0_10

def word276_0_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64]))

def word276_0_78 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_76 word276_0_77

def word276_0_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 256#64)

def word276_0_80 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_78 word276_0_79

def word276_0_81 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_80 word276_0_79

def word276_0_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 16)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 17))

def word276_0_83 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_81 word276_0_82

def word276_0_84 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_83 word276_0_6

def word276_0_85 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_84 word276_0_21

def word276_0_86 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_85 word276_0_23

def word276_0_87 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_86 word276_0_10

def word276_0_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64]))

def word276_0_89 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_87 word276_0_88

def word276_0_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def word276_0_91 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_89 word276_0_90

def word276_0_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def word276_0_93 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_91 word276_0_92

def word276_0_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def word276_0_95 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_93 word276_0_94

def word276_0_96 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 18)) (some 275) ([16, 12, 20, 4, 14]) (some (16, word276_0_17, 276, 19))

def word276_0_97 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_95 word276_0_96

def word276_0_98 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_97 word276_0_6

def word276_0_99 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_98 word276_0_21

def word276_0_100 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_99 word276_0_23

def word276_0_101 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_100 word276_0_10

def word276_0_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64]))

def word276_0_103 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_101 word276_0_102

def word276_0_104 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 20)) (some 177) ([16, 12]) (some (16, word276_0_17, 276, 21))

def word276_0_105 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_103 word276_0_104

def word276_0_106 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_105 word276_0_6

def word276_0_107 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_106 word276_0_21

def word276_0_108 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_107 word276_0_23

def word276_0_109 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_108 word276_0_10

def word276_0_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 104#64]))

def word276_0_111 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_109 word276_0_110

def word276_0_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 22)) (some 177) ([16, 12]) (some (16, word276_0_17, 276, 23))

def word276_0_113 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_111 word276_0_112

def word276_0_114 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_113 word276_0_6

def word276_0_115 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_114 word276_0_21

def word276_0_116 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_115 word276_0_23

def word276_0_117 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_116 word276_0_10

def word276_0_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 112#64]))

def word276_0_119 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_117 word276_0_118

def word276_0_120 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 24)) (some 177) ([16, 12]) (some (16, word276_0_17, 276, 25))

def word276_0_121 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_119 word276_0_120

def word276_0_122 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_121 word276_0_6

def word276_0_123 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_122 word276_0_21

def word276_0_124 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_123 word276_0_23

def word276_0_125 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_124 word276_0_10

def word276_0_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 120#64]))

def word276_0_127 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_125 word276_0_126

def word276_0_128 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 26)) (some 177) ([16, 12]) (some (16, word276_0_17, 276, 27))

def word276_0_129 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_127 word276_0_128

def word276_0_130 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_129 word276_0_6

def word276_0_131 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_130 word276_0_21

def word276_0_132 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_131 word276_0_23

def word276_0_133 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_132 word276_0_10

def word276_0_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 128#64]))

def word276_0_135 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_133 word276_0_134

def word276_0_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 136#64]))

def word276_0_137 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_135 word276_0_136

def word276_0_138 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 28)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 29))

def word276_0_139 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_137 word276_0_138

def word276_0_140 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_139 word276_0_6

def word276_0_141 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_140 word276_0_21

def word276_0_142 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_141 word276_0_23

def word276_0_143 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_142 word276_0_10

def word276_0_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 144#64]))

def word276_0_145 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_143 word276_0_144

def word276_0_146 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_145 word276_0_14

def word276_0_147 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_146 word276_0_14

def word276_0_148 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 30)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 31))

def word276_0_149 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_147 word276_0_148

def word276_0_150 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_149 word276_0_6

def word276_0_151 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_150 word276_0_21

def word276_0_152 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_151 word276_0_23

def word276_0_153 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_152 word276_0_10

def word276_0_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 152#64]))

def word276_0_155 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_153 word276_0_154

def word276_0_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def word276_0_157 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_155 word276_0_156

def word276_0_158 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_157 word276_0_156

def word276_0_159 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 32)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 33))

def word276_0_160 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_158 word276_0_159

def word276_0_161 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_160 word276_0_6

def word276_0_162 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_161 word276_0_21

def word276_0_163 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_162 word276_0_23

def word276_0_164 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_163 word276_0_10

def word276_0_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64]))

def word276_0_166 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_164 word276_0_165

def word276_0_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def word276_0_168 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_166 word276_0_167

def word276_0_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def word276_0_170 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_168 word276_0_169

def word276_0_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def word276_0_172 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_170 word276_0_171

def word276_0_173 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 34)) (some 275) ([16, 12, 20, 4, 14]) (some (16, word276_0_17, 276, 35))

def word276_0_174 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_172 word276_0_173

def word276_0_175 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_174 word276_0_6

def word276_0_176 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_175 word276_0_21

def word276_0_177 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_176 word276_0_23

def word276_0_178 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_177 word276_0_10

def word276_0_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64]))

def word276_0_180 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_178 word276_0_179

def word276_0_181 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_180 word276_0_14

def word276_0_182 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_181 word276_0_14

def word276_0_183 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 36)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 37))

def word276_0_184 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_182 word276_0_183

def word276_0_185 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_184 word276_0_6

def word276_0_186 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_185 word276_0_21

def word276_0_187 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_186 word276_0_23

def word276_0_188 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_187 word276_0_10

def word276_0_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 200#64]))

def word276_0_190 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_188 word276_0_189

def word276_0_191 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 38)) (some 177) ([16, 12]) (some (16, word276_0_17, 276, 39))

def word276_0_192 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_190 word276_0_191

def word276_0_193 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_192 word276_0_6

def word276_0_194 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_193 word276_0_21

def word276_0_195 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_194 word276_0_23

def word276_0_196 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_195 word276_0_10

def word276_0_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 208#64]))

def word276_0_198 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_196 word276_0_197

def word276_0_199 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 40)) (some 177) ([16, 12]) (some (16, word276_0_17, 276, 41))

def word276_0_200 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_198 word276_0_199

def word276_0_201 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_200 word276_0_6

def word276_0_202 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_201 word276_0_21

def word276_0_203 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_202 word276_0_23

def word276_0_204 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_203 word276_0_10

def word276_0_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 216#64]))

def word276_0_206 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_204 word276_0_205

def word276_0_207 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_206 word276_0_14

def word276_0_208 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_207 word276_0_14

def word276_0_209 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 42)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 43))

def word276_0_210 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_208 word276_0_209

def word276_0_211 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_210 word276_0_6

def word276_0_212 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_211 word276_0_21

def word276_0_213 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_212 word276_0_23

def word276_0_214 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_213 word276_0_10

def word276_0_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 224#64]))

def word276_0_216 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_214 word276_0_215

def word276_0_217 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_216 word276_0_14

def word276_0_218 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_217 word276_0_14

def word276_0_219 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 44)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 45))

def word276_0_220 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_218 word276_0_219

def word276_0_221 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_220 word276_0_6

def word276_0_222 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_221 word276_0_21

def word276_0_223 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_222 word276_0_23

def word276_0_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def word276_0_225 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_223 word276_0_224

def word276_0_226 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def word276_0_227 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_225 word276_0_226

def word276_0_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def word276_0_229 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_228 word276_0_6

def word276_0_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def word276_0_231 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_229 word276_0_230

def word276_0_232 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_231 word276_0_10

def word276_0_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 232#64]))

def word276_0_234 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_232 word276_0_233

def word276_0_235 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_234 word276_0_14

def word276_0_236 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_235 word276_0_14

def word276_0_237 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_236 word276_0_14

def word276_0_238 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 46)) (some 176) ([16, 12, 20]) (some (16, word276_0_17, 276, 47))

def word276_0_239 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_237 word276_0_238

def word276_0_240 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_239 word276_0_6

def word276_0_241 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_240 word276_0_21

def word276_0_242 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_241 word276_0_23

def word276_0_243 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_242 word276_0_10

def word276_0_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 240#64]))

def word276_0_245 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_243 word276_0_244

def word276_0_246 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 48)) (some 177) ([16, 12]) (some (16, word276_0_17, 276, 49))

def word276_0_247 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_245 word276_0_246

def word276_0_248 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_247 word276_0_6

def word276_0_249 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_248 word276_0_21

def word276_0_250 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_249 word276_0_23

def word276_0_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def word276_0_252 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_251 word276_0_6

def word276_0_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def word276_0_254 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_252 word276_0_253

def word276_0_255 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 20) word276_0_250 word276_0_254

def word276_0_256 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_227 word276_0_255

def word276_0_257 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_256 word276_0_6

def word276_0_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 9#64]])

def word276_0_259 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_257 word276_0_258

def word276_0_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def word276_0_261 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_259 word276_0_260

def word276_0_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def word276_0_263 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ()))))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 50)) (some 180) ([20]) (some (20, word276_0_262, 276, 51))

def word276_0_264 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_261 word276_0_263

def word276_0_265 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_264 word276_0_6

def word276_0_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 9#64],
      Flapjack.WordLangExpHOL.var 12])

def word276_0_267 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_265 word276_0_266

def word276_0_268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def word276_0_269 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_267 word276_0_268

def word276_0_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def word276_0_271 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_269 word276_0_270

def word276_0_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def word276_0_273 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ()))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
    () Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word276_0_2, 276, 52)) (some 178) ([14, 10]) (some (14, word276_0_272, 276, 53))

def word276_0_274 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_271 word276_0_273

def word276_0_275 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_274 word276_0_6

def word276_0_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 20)

def word276_0_277 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_275 word276_0_276

def word276_0_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 12])

def word276_0_279 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_277 word276_0_278

def word276_0_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4, 14]

def word276_0_281 : WordLangProgHOL (BitVec 64) :=
.seq word276_0_279 word276_0_280

def pass276_0 : WordLangProgHOL (BitVec 64) :=
word276_0_281
theorem pass276_0_eq : WordSimp.compileExp (source276.2.2) = pass276_0 := by
  kernel_rfl
#print axioms pass276_0_eq
end InitECandidate.Proofs.WordStages
