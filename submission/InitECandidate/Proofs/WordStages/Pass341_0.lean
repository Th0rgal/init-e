import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Source341
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word341_0_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def word341_0_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def word341_0_2 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_0 word341_0_1

def word341_0_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def word341_0_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def word341_0_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8, 16, 12]), ((Flapjack.Spt.ls (), Flapjack.Spt.ln)), word341_0_3, 341, 2)) (some 161) ([20, 6]) (some (20, word341_0_4, 341, 3))

def word341_0_6 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_2 word341_0_5

def word341_0_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def word341_0_8 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_6 word341_0_7

def word341_0_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def word341_0_10 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_8 word341_0_9

def word341_0_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def word341_0_12 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_10 word341_0_11

def word341_0_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def word341_0_14 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_13 word341_0_7

def word341_0_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def word341_0_16 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_14 word341_0_15

def word341_0_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 18#64)

def word341_0_18 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_16 word341_0_17

def word341_0_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def word341_0_20 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_18 word341_0_19

def word341_0_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 6#64)

def word341_0_22 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_20 word341_0_21

def word341_0_23 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_22 word341_0_4

def word341_0_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 14) word341_0_23 word341_0_3

def word341_0_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def word341_0_26 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_25 word341_0_7

def word341_0_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def word341_0_28 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_26 word341_0_27

def word341_0_29 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_24 word341_0_28

def word341_0_30 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_12 word341_0_29

def word341_0_31 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_30 word341_0_7

def word341_0_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def word341_0_33 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_31 word341_0_32

def word341_0_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def word341_0_35 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_33 word341_0_34

def word341_0_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20, 6]

def word341_0_37 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_35 word341_0_36

def pass341_0 : WordLangProgHOL (BitVec 64) :=
word341_0_37
theorem pass341_0_eq : WordSimp.compileExp (source341.2.2) = pass341_0 := by
  kernel_rfl
#print axioms pass341_0_eq
end InitECandidate.Proofs.WordStages
