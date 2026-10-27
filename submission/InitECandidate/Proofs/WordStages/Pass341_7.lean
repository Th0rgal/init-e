import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass341_6
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word341_7_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(37, 4), (25, 0), (29, 2), (33, 4)]

def word341_7_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(69, 49), (65, 45), (61, 41), (57, 37)]

def word341_7_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 53), (4, 73), (79, 25)]

def word341_7_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(125, 6), (121, 4), (109, 2), (89, 2), (93, 4), (97, 6), (85, 79)]

def word341_7_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (105, 2), (85, 79)]

def word341_7_243 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_242 word341_2_123

def word341_7_244 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word341_7_241, 341, 2)) (some 161) ([2, 4]) (some (2, word341_7_243, 341, 3))

def word341_7_245 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_158 word341_2_161

def word341_7_246 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_155 word341_7_245

def word341_7_247 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_154 word341_7_246

def word341_7_248 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_152 word341_7_247

def word341_7_249 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_7_248

def word341_7_250 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 129 (Flapjack.WordRegImm.reg 133) word341_7_249 word341_0_3

def word341_7_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 121), (4, 125), (185, 125), (181, 121)]

def word341_7_252 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_251 word341_2_190

def word341_7_253 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_7_252

def word341_7_254 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_7_253

def word341_7_255 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_250 word341_7_254

def word341_7_256 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_146 word341_7_255

def word341_7_257 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_144 word341_7_256

def word341_7_258 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_7_257

def word341_7_259 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_244 word341_7_258

def word341_7_260 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_240 word341_7_259

def word341_7_261 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_99 word341_7_260

def word341_7_262 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_239 word341_7_261

def word341_7_263 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_90 word341_7_262

def word341_7_264 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_87 word341_7_263

def word341_7_265 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_86 word341_7_264

def word341_7_266 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_84 word341_7_265

def word341_7_267 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_238 word341_7_266

def pass341_7 : WordLangProgHOL (BitVec 64) :=
word341_7_267
theorem pass341_7_eq : WordUnreach.removeUnreach (pass341_6) = pass341_7 := by
  kernel_rfl
#print axioms pass341_7_eq
end InitECandidate.Proofs.WordStages
