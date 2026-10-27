import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass341_2
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word341_3_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(89, 2), (93, 4), (97, 6)]

def word341_3_195 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_104 word341_3_194

def word341_3_196 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_109 word341_2_115

def word341_3_197 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_196 word341_2_117

def word341_3_198 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_195 word341_3_197

def word341_3_199 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_127 word341_2_133

def word341_3_200 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_199 word341_2_135

def word341_3_201 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_126 word341_3_200

def word341_3_202 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word341_3_198, 341, 2)) (some 161) ([2, 4]) (some (2, word341_3_201, 341, 3))

def word341_3_203 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_103 word341_3_202

def word341_3_204 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_102 word341_3_203

def word341_3_205 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_101 word341_3_204

def word341_3_206 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_205 word341_0_7

def word341_3_207 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_206 word341_2_144

def word341_3_208 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_207 word341_2_146

def word341_3_209 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_2_152

def word341_3_210 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_209 word341_2_156

def word341_3_211 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_210 word341_2_158

def word341_3_212 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_211 word341_2_161

def word341_3_213 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 129 (Flapjack.WordRegImm.reg 133) word341_3_212 word341_0_3

def word341_3_214 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_213 word341_0_7

def word341_3_215 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_208 word341_3_214

def word341_3_216 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_215 word341_0_7

def word341_3_217 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_216 word341_2_185

def word341_3_218 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_217 word341_2_187

def word341_3_219 : WordLangProgHOL (BitVec 64) :=
.seq word341_3_218 word341_2_191

def word341_3_220 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_82 word341_3_219

def pass341_3 : WordLangProgHOL (BitVec 64) :=
word341_3_220
theorem pass341_3_eq : WordAlloc.removeDeadProg (pass341_2) = pass341_3 := by
  kernel_rfl
#print axioms pass341_3_eq
end InitECandidate.Proofs.WordStages
