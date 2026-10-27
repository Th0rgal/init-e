import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass341_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word341_4_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(61, 41)]

def word341_4_222 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_92 word341_4_221

def word341_4_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(69, 49)]

def word341_4_224 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_95 word341_4_223

def word341_4_225 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_222 word341_4_224

def word341_4_226 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_225 word341_2_99

def word341_4_227 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_91 word341_4_226

def word341_4_228 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_227 word341_3_204

def word341_4_229 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_228 word341_0_7

def word341_4_230 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_229 word341_2_144

def word341_4_231 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_230 word341_2_146

def word341_4_232 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_231 word341_3_214

def word341_4_233 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_232 word341_0_7

def word341_4_234 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_233 word341_2_185

def word341_4_235 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_234 word341_2_187

def word341_4_236 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_235 word341_2_191

def word341_4_237 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_82 word341_4_236

def pass341_4 : WordLangProgHOL (BitVec 64) :=
word341_4_237
theorem pass341_4_eq : WordCse.wordCommonSubexpElim (pass341_3) = pass341_4 := by
  kernel_rfl
#print axioms pass341_4_eq
end InitECandidate.Proofs.WordStages
