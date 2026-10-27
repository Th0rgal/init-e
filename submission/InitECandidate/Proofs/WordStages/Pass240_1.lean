import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass240_0
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word240_1_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 14 64#64)

def word240_1_90 : WordLangProgHOL (BitVec 64) :=
.seq word240_0_4 word240_1_89

def word240_1_91 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_89 word240_0_8

def word240_1_92 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_90 word240_1_91

def word240_1_93 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_92 word240_0_3

def word240_1_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(22, 2)]

def word240_1_95 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_93 word240_1_94

def word240_1_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(8, 4)]

def word240_1_97 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_95 word240_1_96

def word240_1_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(16, 18)]

def word240_1_99 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_97 word240_1_98

def word240_1_100 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_99 word240_0_19

def word240_1_101 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_100 word240_0_3

def word240_1_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(23, 18)]

def word240_1_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 14 23 (Flapjack.WordRegImm.imm 32#64)))

def word240_1_104 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_102 word240_1_103

def word240_1_105 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_101 word240_1_104

def word240_1_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(8, 14)]

def word240_1_107 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_105 word240_1_106

def word240_1_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 16 32#64)

def word240_1_109 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_107 word240_1_108

def word240_1_110 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_108 word240_0_29

def word240_1_111 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_109 word240_1_110

def word240_1_112 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_111 word240_0_3

def word240_1_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 22 0#64)

def word240_1_114 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_112 word240_1_113

def word240_1_115 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_114 word240_0_3

def word240_1_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(16, 22)]

def word240_1_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(12, 4)]

def word240_1_118 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_116 word240_1_117

def word240_1_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 16 1#64)

def word240_1_120 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_119 word240_0_3

def word240_1_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 20 1#64)

def word240_1_122 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_120 word240_1_121

def word240_1_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(23, 22)]

def word240_1_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsr 23 23 (Flapjack.WordRegImm.imm 3#64)))

def word240_1_125 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_123 word240_1_124

def word240_1_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(24, 14)]

def word240_1_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 8 23 (Flapjack.WordRegImm.reg 24)))

def word240_1_128 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_126 word240_1_127

def word240_1_129 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_125 word240_1_128

def word240_1_130 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_122 word240_1_129

def word240_1_131 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_130 word240_0_45

def word240_1_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 16 23 (Flapjack.WordRegImm.reg 24)))

def word240_1_133 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_126 word240_1_132

def word240_1_134 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_125 word240_1_133

def word240_1_135 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_131 word240_1_134

def word240_1_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 23 1#64)

def word240_1_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(24, 22)]

def word240_1_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.and 24 24 (Flapjack.WordRegImm.imm 7#64)))

def word240_1_139 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_137 word240_1_138

def word240_1_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 23 23 (Flapjack.WordRegImm.reg 24)))

def word240_1_141 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_139 word240_1_140

def word240_1_142 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_136 word240_1_141

def word240_1_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(24, 8)]

def word240_1_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.or 12 23 (Flapjack.WordRegImm.reg 24)))

def word240_1_145 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_143 word240_1_144

def word240_1_146 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_142 word240_1_145

def word240_1_147 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_135 word240_1_146

def word240_1_148 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_147 word240_0_51

def word240_1_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 8 23 (Flapjack.WordRegImm.imm 1#64)))

def word240_1_150 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_123 word240_1_149

def word240_1_151 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_148 word240_1_150

def word240_1_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(22, 8)]

def word240_1_153 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_151 word240_1_152

def word240_1_154 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_153 word240_0_57

def word240_1_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 16 0#64)

def word240_1_156 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_155 word240_0_3

def word240_1_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 20 0#64)

def word240_1_158 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_156 word240_1_157

def word240_1_159 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_158 word240_0_63

def word240_1_160 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 16 (Flapjack.WordRegImm.reg 12) word240_1_154 word240_1_159

def word240_1_161 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_118 word240_1_160

def word240_1_162 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_161 word240_0_3

def word240_1_163 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())) ()
      (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())))
    () (Flapjack.Spt.ls ()))
  () Flapjack.Spt.ln) word240_1_162 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls ()) () (Flapjack.Spt.bs Flapjack.Spt.ln () (Flapjack.Spt.ls ())))
    Flapjack.Spt.ln)
  () Flapjack.Spt.ln)

def word240_1_164 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_115 word240_1_163

def word240_1_165 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_164 word240_0_3

def word240_1_166 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_165 word240_1_98

def word240_1_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(12, 14)]

def word240_1_168 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_166 word240_1_167

def word240_1_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(20, 6)]

def word240_1_170 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_168 word240_1_169

def word240_1_171 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_170 word240_0_77

def word240_1_172 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_171 word240_0_3

def word240_1_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(16, 10)]

def word240_1_174 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_172 word240_1_173

def word240_1_175 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_174 word240_0_82

def word240_1_176 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_175 word240_0_3

def word240_1_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 8 0#64)

def word240_1_178 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_176 word240_1_177

def word240_1_179 : WordLangProgHOL (BitVec 64) :=
.seq word240_1_178 word240_0_87

def pass240_1 : WordLangProgHOL (BitVec 64) :=
word240_1_179
theorem pass240_1_eq : WordInst.instSelectExecutable riscvConfig (maxVarHOL (pass240_0) + 1) (pass240_0) = pass240_1 := by
  kernel_rfl
#print axioms pass240_1_eq
end InitECandidate.Proofs.WordStages
