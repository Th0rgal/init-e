import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass270_0
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word270_1_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(16, 2)]

def word270_1_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(12, 4)]

def word270_1_76 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_74 word270_1_75

def word270_1_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 20 0#64)

def word270_1_78 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_76 word270_1_77

def word270_1_79 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_78 word270_1_77

def word270_1_80 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_79 word270_0_8

def word270_1_81 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_80 word270_0_10

def word270_1_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 12 8#64)

def word270_1_83 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_81 word270_1_82

def word270_1_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(20, 8)]

def word270_1_85 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_83 word270_1_84

def word270_1_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 12 1#64)

def word270_1_87 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_86 word270_0_10

def word270_1_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 6 1#64)

def word270_1_89 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_87 word270_1_88

def word270_1_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 16 4#64)

def word270_1_91 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_89 word270_1_90

def word270_1_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(21, 16)]

def word270_1_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 21)

def word270_1_94 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_92 word270_1_93

def word270_1_95 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_91 word270_1_94

def word270_1_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 16 3#64)

def word270_1_97 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_95 word270_1_96

def word270_1_98 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_97 word270_0_7

def word270_1_99 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 20) word270_1_98 word270_0_6

def word270_1_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 12 0#64)

def word270_1_101 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_100 word270_0_10

def word270_1_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 6 0#64)

def word270_1_103 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_101 word270_1_102

def word270_1_104 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_99 word270_1_103

def word270_1_105 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_85 word270_1_104

def word270_1_106 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_105 word270_0_10

def word270_1_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 16 0#64)

def word270_1_108 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_106 word270_1_107

def word270_1_109 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_108 word270_1_100

def word270_1_110 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_109 word270_0_10

def word270_1_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(6, 12)]

def word270_1_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(14, 8)]

def word270_1_113 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_111 word270_1_112

def word270_1_114 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_88 word270_0_10

def word270_1_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 10 1#64)

def word270_1_116 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_114 word270_1_115

def word270_1_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(21, 12)]

def word270_1_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(22, 18)]

def word270_1_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 20 21 (Flapjack.WordRegImm.reg 22)))

def word270_1_120 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_118 word270_1_119

def word270_1_121 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_117 word270_1_120

def word270_1_122 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_116 word270_1_121

def word270_1_123 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_122 word270_0_47

def word270_1_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(21, 20)]

def word270_1_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(22, 16)]

def word270_1_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 22 22 (Flapjack.WordRegImm.imm 8#64)))

def word270_1_127 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_125 word270_1_126

def word270_1_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.or 6 21 (Flapjack.WordRegImm.reg 22)))

def word270_1_129 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_127 word270_1_128

def word270_1_130 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_124 word270_1_129

def word270_1_131 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_123 word270_1_130

def word270_1_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(16, 6)]

def word270_1_133 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_131 word270_1_132

def word270_1_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 20 21 (Flapjack.WordRegImm.imm 1#64)))

def word270_1_135 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_117 word270_1_134

def word270_1_136 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_133 word270_1_135

def word270_1_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(12, 20)]

def word270_1_138 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_136 word270_1_137

def word270_1_139 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_138 word270_0_57

def word270_1_140 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_102 word270_0_10

def word270_1_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 10 0#64)

def word270_1_142 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_140 word270_1_141

def word270_1_143 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_142 word270_0_62

def word270_1_144 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.WordRegImm.reg 14) word270_1_139 word270_1_143

def word270_1_145 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_113 word270_1_144

def word270_1_146 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_145 word270_0_10

def word270_1_147 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))) ()
    (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ()))))
  () Flapjack.Spt.ln) word270_1_146 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ()))))
  () Flapjack.Spt.ln)

def word270_1_148 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_110 word270_1_147

def word270_1_149 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_148 word270_0_10

def word270_1_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(20, 16)]

def word270_1_151 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_149 word270_1_150

def word270_1_152 : WordLangProgHOL (BitVec 64) :=
.seq word270_1_151 word270_0_72

def pass270_1 : WordLangProgHOL (BitVec 64) :=
word270_1_152
theorem pass270_1_eq : WordInst.instSelectExecutable riscvConfig (maxVarHOL (pass270_0) + 1) (pass270_0) = pass270_1 := by
  kernel_rfl
#print axioms pass270_1_eq
end InitECandidate.Proofs.WordStages
