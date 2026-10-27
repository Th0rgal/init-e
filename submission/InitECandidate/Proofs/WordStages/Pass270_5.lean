import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass270_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word270_5_363 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(281, 169), (277, 181), (273, 189)]

def word270_5_364 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_346 word270_5_363

def word270_5_365 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 193 (Flapjack.WordRegImm.reg 197) word270_5_364 word270_3_351

def word270_5_366 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_245 word270_5_365

def word270_5_367 : WordLangProgHOL (BitVec 64) :=
.seq word270_5_366 word270_0_10

def word270_5_368 : WordLangProgHOL (BitVec 64) :=
.seq word270_5_367 word270_2_303

def word270_5_369 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          Flapjack.Spt.ln)))
    Flapjack.Spt.ln)) word270_5_368 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    Flapjack.Spt.ln))

def word270_5_370 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_241 word270_5_369

def word270_5_371 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_339 word270_5_370

def word270_5_372 : WordLangProgHOL (BitVec 64) :=
.seq word270_5_371 word270_0_10

def word270_5_373 : WordLangProgHOL (BitVec 64) :=
.seq word270_5_372 word270_2_309

def word270_5_374 : WordLangProgHOL (BitVec 64) :=
.seq word270_5_373 word270_2_313

def word270_5_375 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_153 word270_5_374

def pass270_5 : WordLangProgHOL (BitVec 64) :=
word270_5_375
theorem pass270_5_eq : WordCopy.copyProp (pass270_4) = pass270_5 := by
  kernel_rfl
#print axioms pass270_5_eq
end InitECandidate.Proofs.WordStages
