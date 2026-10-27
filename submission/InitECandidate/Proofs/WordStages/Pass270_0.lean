import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Source270
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word270_0_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def word270_0_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def word270_0_2 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_0 word270_0_1

def word270_0_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def word270_0_4 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_2 word270_0_3

def word270_0_5 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_4 word270_0_3

def word270_0_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def word270_0_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def word270_0_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())) () Flapjack.Spt.ln, Flapjack.Spt.ln)), word270_0_6, 270, 2)) (some 269) ([16, 12, 20]) (some (16, word270_0_7, 270, 3))

def word270_0_9 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_5 word270_0_8

def word270_0_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def word270_0_11 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_9 word270_0_10

def word270_0_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 8#64)

def word270_0_13 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_11 word270_0_12

def word270_0_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def word270_0_15 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_13 word270_0_14

def word270_0_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def word270_0_17 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_16 word270_0_10

def word270_0_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def word270_0_19 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_17 word270_0_18

def word270_0_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 4#64)

def word270_0_21 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_19 word270_0_20

def word270_0_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def word270_0_23 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_21 word270_0_22

def word270_0_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 3#64)

def word270_0_25 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_23 word270_0_24

def word270_0_26 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_25 word270_0_7

def word270_0_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 20) word270_0_26 word270_0_6

def word270_0_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def word270_0_29 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_28 word270_0_10

def word270_0_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def word270_0_31 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_29 word270_0_30

def word270_0_32 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_27 word270_0_31

def word270_0_33 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_15 word270_0_32

def word270_0_34 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_33 word270_0_10

def word270_0_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def word270_0_36 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_34 word270_0_35

def word270_0_37 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_36 word270_0_28

def word270_0_38 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_37 word270_0_10

def word270_0_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def word270_0_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def word270_0_41 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_39 word270_0_40

def word270_0_42 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_18 word270_0_10

def word270_0_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def word270_0_44 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_42 word270_0_43

def word270_0_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 12])

def word270_0_46 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_44 word270_0_45

def word270_0_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 20 (Flapjack.WordLangAddr.addr 20 0#64))

def word270_0_48 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_46 word270_0_47

def word270_0_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.var 20])

def word270_0_50 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_48 word270_0_49

def word270_0_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def word270_0_52 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_50 word270_0_51

def word270_0_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def word270_0_54 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_52 word270_0_53

def word270_0_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def word270_0_56 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_54 word270_0_55

def word270_0_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def word270_0_58 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_56 word270_0_57

def word270_0_59 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_30 word270_0_10

def word270_0_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def word270_0_61 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_59 word270_0_60

def word270_0_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def word270_0_63 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_61 word270_0_62

def word270_0_64 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.WordRegImm.reg 14) word270_0_58 word270_0_63

def word270_0_65 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_41 word270_0_64

def word270_0_66 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_65 word270_0_10

def word270_0_67 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
    (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ()))))
  () Flapjack.Spt.ln) word270_0_66 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
  () Flapjack.Spt.ln)

def word270_0_68 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_38 word270_0_67

def word270_0_69 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_68 word270_0_10

def word270_0_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def word270_0_71 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_69 word270_0_70

def word270_0_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def word270_0_73 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_71 word270_0_72

def pass270_0 : WordLangProgHOL (BitVec 64) :=
word270_0_73
theorem pass270_0_eq : WordSimp.compileExp (source270.2.2) = pass270_0 := by
  kernel_rfl
#print axioms pass270_0_eq
end InitECandidate.Proofs.WordStages
