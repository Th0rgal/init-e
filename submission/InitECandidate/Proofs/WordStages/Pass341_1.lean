import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass341_0
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word341_1_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(21, 4)]

def word341_1_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 21 21 (Flapjack.WordRegImm.imm 4#64)))

def word341_1_40 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_38 word341_1_39

def word341_1_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(22, 2)]

def word341_1_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 21 21 (Flapjack.WordRegImm.reg 22)))

def word341_1_43 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_41 word341_1_42

def word341_1_44 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_40 word341_1_43

def word341_1_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 20 (Flapjack.WordLangAddr.addr 21 0#64))

def word341_1_46 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_44 word341_1_45

def word341_1_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 6 (Flapjack.WordLangAddr.addr 21 8#64))

def word341_1_48 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_44 word341_1_47

def word341_1_49 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_46 word341_1_48

def word341_1_50 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_49 word341_0_5

def word341_1_51 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_50 word341_0_7

def word341_1_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6, 18)]

def word341_1_53 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_51 word341_1_52

def word341_1_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 14 1#64)

def word341_1_55 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_53 word341_1_54

def word341_1_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 6 1#64)

def word341_1_57 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_56 word341_0_7

def word341_1_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 10 1#64)

def word341_1_59 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_57 word341_1_58

def word341_1_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 20 18#64)

def word341_1_61 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_59 word341_1_60

def word341_1_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(21, 20)]

def word341_1_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 21)

def word341_1_64 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_62 word341_1_63

def word341_1_65 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_61 word341_1_64

def word341_1_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 20 6#64)

def word341_1_67 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_65 word341_1_66

def word341_1_68 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_67 word341_0_4

def word341_1_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 14) word341_1_68 word341_0_3

def word341_1_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 6 0#64)

def word341_1_71 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_70 word341_0_7

def word341_1_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 10 0#64)

def word341_1_73 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_71 word341_1_72

def word341_1_74 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_69 word341_1_73

def word341_1_75 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_55 word341_1_74

def word341_1_76 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_75 word341_0_7

def word341_1_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(20, 8)]

def word341_1_78 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_76 word341_1_77

def word341_1_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6, 16)]

def word341_1_80 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_78 word341_1_79

def word341_1_81 : WordLangProgHOL (BitVec 64) :=
.seq word341_1_80 word341_0_36

def pass341_1 : WordLangProgHOL (BitVec 64) :=
word341_1_81
theorem pass341_1_eq : WordInst.instSelectExecutable riscvConfig (maxVarHOL (pass341_0) + 1) (pass341_0) = pass341_1 := by
  kernel_rfl
#print axioms pass341_1_eq
end InitECandidate.Proofs.WordStages
