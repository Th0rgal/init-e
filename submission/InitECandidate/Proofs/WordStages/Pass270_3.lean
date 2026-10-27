import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass270_2
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word270_3_316 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_156 word270_2_159

def word270_3_317 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_163 word270_2_164

def word270_3_318 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_168 word270_2_170

def word270_3_319 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_317 word270_3_318

def word270_3_320 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_182 word270_2_184

def word270_3_321 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_181 word270_3_320

def word270_3_322 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))))),
  Flapjack.Spt.ln)), word270_3_319, 270, 2)) (some 269) ([2, 4, 6]) (some (2, word270_3_321, 270, 3))

def word270_3_323 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_162 word270_3_322

def word270_3_324 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_161 word270_3_323

def word270_3_325 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_316 word270_3_324

def word270_3_326 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_325 word270_0_10

def word270_3_327 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_326 word270_2_195

def word270_3_328 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_327 word270_2_197

def word270_3_329 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_2_203

def word270_3_330 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_329 word270_2_207

def word270_3_331 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_330 word270_2_209

def word270_3_332 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_331 word270_2_212

def word270_3_333 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 105 (Flapjack.WordRegImm.reg 109) word270_3_332 word270_0_6

def word270_3_334 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_333 word270_0_10

def word270_3_335 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_328 word270_3_334

def word270_3_336 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_335 word270_0_10

def word270_3_337 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_336 word270_2_236

def word270_3_338 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_337 word270_2_238

def word270_3_339 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_338 word270_0_10

def word270_3_340 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_2_254

def word270_3_341 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_340 word270_2_256

def word270_3_342 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_341 word270_2_264

def word270_3_343 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_342 word270_2_266

def word270_3_344 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_343 word270_2_270

def word270_3_345 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_344 word270_2_272

def word270_3_346 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_345 word270_2_275

def word270_3_347 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(281, 241), (277, 253), (273, 213)]

def word270_3_348 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_346 word270_3_347

def word270_3_349 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_0_62

def word270_3_350 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(281, 169), (277, 193), (273, 189)]

def word270_3_351 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_349 word270_3_350

def word270_3_352 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 193 (Flapjack.WordRegImm.reg 197) word270_3_348 word270_3_351

def word270_3_353 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_245 word270_3_352

def word270_3_354 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_353 word270_0_10

def word270_3_355 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_354 word270_2_303

def word270_3_356 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word270_3_355 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word270_3_357 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_241 word270_3_356

def word270_3_358 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_339 word270_3_357

def word270_3_359 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_358 word270_0_10

def word270_3_360 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_359 word270_2_309

def word270_3_361 : WordLangProgHOL (BitVec 64) :=
.seq word270_3_360 word270_2_313

def word270_3_362 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_153 word270_3_361

def pass270_3 : WordLangProgHOL (BitVec 64) :=
word270_3_362
theorem pass270_3_eq : WordAlloc.removeDeadProg (pass270_2) = pass270_3 := by
  kernel_rfl
#print axioms pass270_3_eq
end InitECandidate.Proofs.WordStages
