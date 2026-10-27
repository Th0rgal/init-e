import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass341_7
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word341_8_268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(37, 4), (25, 0), (29, 2)]

def word341_8_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(125, 6), (121, 4), (109, 2), (85, 79)]

def word341_8_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (85, 79)]

def word341_8_271 : WordLangProgHOL (BitVec 64) :=
.seq word341_8_270 word341_2_123

def word341_8_272 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word341_8_269, 341, 2)) (some 161) ([2, 4]) (some (2, word341_8_271, 341, 3))

def word341_8_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 121), (4, 125)]

def word341_8_274 : WordLangProgHOL (BitVec 64) :=
.seq word341_8_273 word341_2_190

def word341_8_275 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_8_274

def word341_8_276 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_8_275

def word341_8_277 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_250 word341_8_276

def word341_8_278 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_146 word341_8_277

def word341_8_279 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_144 word341_8_278

def word341_8_280 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_8_279

def word341_8_281 : WordLangProgHOL (BitVec 64) :=
.seq word341_8_272 word341_8_280

def word341_8_282 : WordLangProgHOL (BitVec 64) :=
.seq word341_7_240 word341_8_281

def word341_8_283 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_99 word341_8_282

def word341_8_284 : WordLangProgHOL (BitVec 64) :=
.seq word341_4_223 word341_8_283

def word341_8_285 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_90 word341_8_284

def word341_8_286 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_87 word341_8_285

def word341_8_287 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_86 word341_8_286

def word341_8_288 : WordLangProgHOL (BitVec 64) :=
.seq word341_2_84 word341_8_287

def word341_8_289 : WordLangProgHOL (BitVec 64) :=
.seq word341_8_268 word341_8_288

def pass341_8 : WordLangProgHOL (BitVec 64) :=
word341_8_289
theorem pass341_8_eq : WordAlloc.removeDeadProg (pass341_7) = pass341_8 := by
  kernel_rfl
#print axioms pass341_8_eq
end InitECandidate.Proofs.WordStages
