import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass270_6
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word270_7_376 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(41, 4), (37, 2), (25, 0), (29, 2), (33, 4)]

def word270_7_377 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 37), (4, 41), (6, 49), (55, 25), (59, 41), (63, 37)]

def word270_7_378 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(97, 4), (93, 2), (81, 2), (85, 4), (69, 55), (73, 59), (77, 63)]

def word270_7_379 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (89, 2), (69, 55), (73, 59), (77, 63)]

def word270_7_380 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_379 word270_2_178

def word270_7_381 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))))),
  Flapjack.Spt.ln)), word270_7_378, 270, 2)) (some 269) ([2, 4, 6]) (some (2, word270_7_380, 270, 3))

def word270_7_382 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_209 word270_2_212

def word270_7_383 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_206 word270_7_382

def word270_7_384 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_205 word270_7_383

def word270_7_385 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_203 word270_7_384

def word270_7_386 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_7_385

def word270_7_387 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 105 (Flapjack.WordRegImm.reg 109) word270_7_386 word270_0_6

def word270_7_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(197, 173), (193, 181)]

def word270_7_389 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(213, 189), (209, 193)]

def word270_7_390 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(229, 169), (225, 221)]

def word270_7_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(245, 209), (241, 237)]

def word270_7_392 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(169, 241), (173, 197), (181, 249), (189, 213), (253, 249)]

def word270_7_393 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_392 word270_0_57

def word270_7_394 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_269 word270_7_393

def word270_7_395 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_391 word270_7_394

def word270_7_396 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_262 word270_7_395

def word270_7_397 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_260 word270_7_396

def word270_7_398 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_390 word270_7_397

def word270_7_399 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_256 word270_7_398

def word270_7_400 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_252 word270_7_399

def word270_7_401 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_389 word270_7_400

def word270_7_402 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_7_401

def word270_7_403 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 193 (Flapjack.WordRegImm.reg 197) word270_7_402 word270_3_349

def word270_7_404 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_2_303

def word270_7_405 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_403 word270_7_404

def word270_7_406 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_388 word270_7_405

def word270_7_407 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word270_7_406 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word270_7_408 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 169), (297, 169)]

def word270_7_409 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_408 word270_2_312

def word270_7_410 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_7_409

def word270_7_411 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_407 word270_7_410

def word270_7_412 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_241 word270_7_411

def word270_7_413 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_7_412

def word270_7_414 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_238 word270_7_413

def word270_7_415 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_236 word270_7_414

def word270_7_416 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_7_415

def word270_7_417 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_7_416

def word270_7_418 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_387 word270_7_417

def word270_7_419 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_197 word270_7_418

def word270_7_420 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_195 word270_7_419

def word270_7_421 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_10 word270_7_420

def word270_7_422 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_381 word270_7_421

def word270_7_423 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_377 word270_7_422

def word270_7_424 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_159 word270_7_423

def word270_7_425 : WordLangProgHOL (BitVec 64) :=
.seq word270_7_376 word270_7_424

def pass270_7 : WordLangProgHOL (BitVec 64) :=
word270_7_425
theorem pass270_7_eq : WordUnreach.removeUnreach (pass270_6) = pass270_7 := by
  kernel_rfl
#print axioms pass270_7_eq
end InitECandidate.Proofs.WordStages
