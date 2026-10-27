import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SmallSsaKernelComputation
import InitECandidate.Proofs.WordStages.Pass341_1
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word341_2_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(25, 0), (29, 2), (33, 4)]

def word341_2_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(37, 33)]

def word341_2_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 41 37 (Flapjack.WordRegImm.imm 4#64)))

def word341_2_85 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_83 word341_2_84

def word341_2_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(45, 29)]

def word341_2_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 49 41 (Flapjack.WordRegImm.reg 45)))

def word341_2_88 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_86 word341_2_87

def word341_2_89 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_85 word341_2_88

def word341_2_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 53 (Flapjack.WordLangAddr.addr 49 0#64))

def word341_2_91 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_89 word341_2_90

def word341_2_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(57, 37)]

def word341_2_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 61 57 (Flapjack.WordRegImm.imm 4#64)))

def word341_2_94 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_92 word341_2_93

def word341_2_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(65, 45)]

def word341_2_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 69 61 (Flapjack.WordRegImm.reg 65)))

def word341_2_97 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_95 word341_2_96

def word341_2_98 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_94 word341_2_97

def word341_2_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 73 (Flapjack.WordLangAddr.addr 69 8#64))

def word341_2_100 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_98 word341_2_99

def word341_2_101 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_91 word341_2_100

def word341_2_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(79, 25)]

def word341_2_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 53), (4, 73)]

def word341_2_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(85, 79)]

def word341_2_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(89, 2), (93, 4), (97, 6), (101, 8)]

def word341_2_106 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_105 word341_0_3

def word341_2_107 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_104 word341_2_106

def word341_2_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 []

def word341_2_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(109, 89)]

def word341_2_110 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_3 word341_2_109

def word341_2_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(113, 101)]

def word341_2_112 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_110 word341_2_111

def word341_2_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 117 0#64)

def word341_2_114 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_112 word341_2_113

def word341_2_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(121, 93)]

def word341_2_116 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_114 word341_2_115

def word341_2_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(125, 97)]

def word341_2_118 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_116 word341_2_117

def word341_2_119 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_108 word341_2_118

def word341_2_120 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_107 word341_2_119

def word341_2_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(105, 2)]

def word341_2_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 105)]

def word341_2_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def word341_2_124 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_122 word341_2_123

def word341_2_125 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_121 word341_2_124

def word341_2_126 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_104 word341_2_125

def word341_2_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 109 0#64)

def word341_2_128 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_3 word341_2_127

def word341_2_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 113 0#64)

def word341_2_130 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_128 word341_2_129

def word341_2_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(117, 105)]

def word341_2_132 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_130 word341_2_131

def word341_2_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 121 0#64)

def word341_2_134 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_132 word341_2_133

def word341_2_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 125 0#64)

def word341_2_136 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_134 word341_2_135

def word341_2_137 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_108 word341_2_136

def word341_2_138 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_126 word341_2_137

def word341_2_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word341_2_120, 341, 2)) (some 161) ([2, 4]) (some (2, word341_2_138, 341, 3))

def word341_2_140 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_103 word341_2_139

def word341_2_141 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_102 word341_2_140

def word341_2_142 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_101 word341_2_141

def word341_2_143 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_142 word341_0_7

def word341_2_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(129, 109)]

def word341_2_145 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_143 word341_2_144

def word341_2_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 133 1#64)

def word341_2_147 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_145 word341_2_146

def word341_2_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 137 1#64)

def word341_2_149 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_148 word341_0_7

def word341_2_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 141 1#64)

def word341_2_151 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_149 word341_2_150

def word341_2_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 145 18#64)

def word341_2_153 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_151 word341_2_152

def word341_2_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(149, 145)]

def word341_2_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 149)

def word341_2_156 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_154 word341_2_155

def word341_2_157 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_153 word341_2_156

def word341_2_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 153 6#64)

def word341_2_159 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_157 word341_2_158

def word341_2_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 153)]

def word341_2_161 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_160 word341_2_123

def word341_2_162 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_159 word341_2_161

def word341_2_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(161, 153), (157, 137)]

def word341_2_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(165, 141)]

def word341_2_165 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_3 word341_2_164

def word341_2_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(169, 149)]

def word341_2_167 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_165 word341_2_166

def word341_2_168 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_163 word341_2_167

def word341_2_169 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_162 word341_2_168

def word341_2_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 2 [(161, 117), (157, 129)]

def word341_2_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 165 0#64)

def word341_2_172 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_3 word341_2_171

def word341_2_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 169 0#64)

def word341_2_174 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_172 word341_2_173

def word341_2_175 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_170 word341_2_174

def word341_2_176 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_3 word341_2_175

def word341_2_177 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 129 (Flapjack.WordRegImm.reg 133) word341_2_169 word341_2_176

def word341_2_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 173 0#64)

def word341_2_179 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_178 word341_0_7

def word341_2_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 177 0#64)

def word341_2_181 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_179 word341_2_180

def word341_2_182 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_177 word341_2_181

def word341_2_183 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_147 word341_2_182

def word341_2_184 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_183 word341_0_7

def word341_2_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(181, 121)]

def word341_2_186 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_184 word341_2_185

def word341_2_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(185, 125)]

def word341_2_188 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_186 word341_2_187

def word341_2_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 181), (4, 185)]

def word341_2_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 85 [2, 4]

def word341_2_191 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_189 word341_2_190

def word341_2_192 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_188 word341_2_191

def word341_2_193 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_82 word341_2_192

def pass341_2 : WordLangProgHOL (BitVec 64) :=
word341_2_193
theorem pass341_2_eq : WordAlloc.fullSsaCcTrans 3 (pass341_1) = pass341_2 := by
  rw [InitECandidate.Proofs.SmallSsaKernelComputation.fullSsaStructural_eq]
  kernel_rfl
#print axioms pass341_2_eq
end InitECandidate.Proofs.WordStages
