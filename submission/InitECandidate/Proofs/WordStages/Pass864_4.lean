import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass864_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word864_4_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(185, 157)]

def word864_4_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(189, 161)]

def word864_4_49 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_47 word864_4_48

def word864_4_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(193, 165)]

def word864_4_51 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_49 word864_4_50

def word864_4_53 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_51 word864_2_65

def word864_4_54 : WordLangProgHOL (BitVec 64) :=
.seq word864_3_46 word864_4_53

def word864_4_56 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_54 word864_2_70

def word864_4_68 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_56 word864_3_67

def word864_4_69 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_68 word864_0_10

def word864_4_75 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_69 word864_2_104

def word864_4_93 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_75 word864_3_92

def word864_4_94 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_93 word864_0_10

def word864_4_104 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_94 word864_2_142

def word864_4_106 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_104 word864_2_144

def word864_4_108 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_106 word864_2_146

def word864_4_112 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_108 word864_2_150

def word864_4_118 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_112 word864_2_156

def word864_4_136 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_118 word864_3_135

def word864_4_137 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_136 word864_0_10

def word864_4_147 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_137 word864_2_194

def word864_4_149 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_147 word864_2_196

def word864_4_151 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_149 word864_2_198

def word864_4_155 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_151 word864_2_202

def word864_4_157 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_155 word864_2_208

def word864_4_159 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_157 word864_2_210

def word864_4_177 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_159 word864_3_176

def word864_4_178 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_177 word864_0_10

def word864_4_188 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_178 word864_2_248

def word864_4_190 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_188 word864_2_250

def word864_4_192 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_190 word864_2_252

def word864_4_196 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_192 word864_2_256

def word864_4_198 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_196 word864_2_260

def word864_4_216 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_198 word864_3_215

def word864_4_217 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_216 word864_0_10

def word864_4_227 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_217 word864_2_298

def word864_4_229 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_227 word864_2_300

def word864_4_231 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_229 word864_2_302

def word864_4_235 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_231 word864_2_306

def word864_4_237 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_235 word864_2_312

def word864_4_239 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_237 word864_2_314

def word864_4_257 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_239 word864_3_256

def word864_4_258 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_257 word864_0_10

def word864_4_268 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_258 word864_2_352

def word864_4_270 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_268 word864_2_354

def word864_4_272 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_270 word864_2_356

def word864_4_276 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_272 word864_2_360

def word864_4_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(873, 841)]

def word864_4_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(877, 845)]

def word864_4_279 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_277 word864_4_278

def word864_4_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(881, 849)]

def word864_4_281 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_279 word864_4_280

def word864_4_283 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_281 word864_2_367

def word864_4_285 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_283 word864_2_369

def word864_4_286 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_276 word864_4_285

def word864_4_288 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_286 word864_2_372

def word864_4_290 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_288 word864_2_374

def word864_4_294 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_290 word864_2_378

def word864_4_304 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_294 word864_3_303

def word864_4_305 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_304 word864_0_10

def word864_4_313 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_305 word864_2_413

def word864_4_317 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_313 word864_2_417

def word864_4_319 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_317 word864_2_421

def word864_4_331 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_319 word864_3_330

def word864_4_332 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_331 word864_0_10

def word864_4_340 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_332 word864_2_457

def word864_4_342 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_340 word864_2_459

def word864_4_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1157, 1137)]

def word864_4_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1161, 1141)]

def word864_4_345 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_343 word864_4_344

def word864_4_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1165, 1145)]

def word864_4_347 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_345 word864_4_346

def word864_4_349 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_347 word864_2_466

def word864_4_350 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_342 word864_4_349

def word864_4_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1181, 1157)]

def word864_4_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1185, 1161)]

def word864_4_353 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_351 word864_4_352

def word864_4_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1189, 1165)]

def word864_4_355 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_353 word864_4_354

def word864_4_356 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1193, 1169)]

def word864_4_357 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_355 word864_4_356

def word864_4_359 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_357 word864_2_480

def word864_4_361 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_359 word864_2_482

def word864_4_362 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1205, 1181)]

def word864_4_363 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1209, 1185)]

def word864_4_364 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_362 word864_4_363

def word864_4_365 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1213, 1189)]

def word864_4_366 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_364 word864_4_365

def word864_4_368 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_366 word864_2_489

def word864_4_370 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_368 word864_2_491

def word864_4_371 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_361 word864_4_370

def word864_4_372 : WordLangProgHOL (BitVec 64) :=
.seq word864_0_10 word864_4_371

def word864_4_374 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_372 word864_3_373

def word864_4_377 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 1153 (Flapjack.WordRegImm.reg 1169) word864_4_374 word864_3_376

def word864_4_378 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_350 word864_4_377

def word864_4_379 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_378 word864_0_10

def word864_4_380 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1253, 1137)]

def word864_4_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1257, 1141)]

def word864_4_382 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_380 word864_4_381

def word864_4_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1261, 1145)]

def word864_4_384 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_382 word864_4_383

def word864_4_386 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_384 word864_2_517

def word864_4_387 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_379 word864_4_386

def word864_4_389 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_387 word864_2_520

def word864_4_391 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_389 word864_2_524

def word864_4_403 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_391 word864_3_402

def word864_4_404 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_403 word864_0_10

def word864_4_414 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_404 word864_3_413

def word864_4_415 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_414 word864_0_10

def word864_4_417 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_415 word864_2_583

def word864_4_429 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_417 word864_3_428

def word864_4_430 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_429 word864_0_10

def word864_4_434 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_430 word864_2_615

def word864_4_436 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_434 word864_2_617

def word864_4_437 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_436 word864_0_10

def word864_4_453 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1717, 1697)]

def word864_4_454 : WordLangProgHOL (BitVec 64) :=
.seq word864_2_639 word864_4_453

def word864_4_456 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1725, 1705)]

def word864_4_457 : WordLangProgHOL (BitVec 64) :=
.seq word864_2_642 word864_4_456

def word864_4_458 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_454 word864_4_457

def word864_4_460 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_458 word864_2_646

def word864_4_461 : WordLangProgHOL (BitVec 64) :=
.seq word864_3_451 word864_4_460

def word864_4_479 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_461 word864_3_478

def word864_4_480 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_479 word864_0_10

def word864_4_482 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_480 word864_2_677

def word864_4_484 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_482 word864_2_679

def word864_4_496 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_484 word864_3_495

def word864_4_497 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_496 word864_0_10

def word864_4_501 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_497 word864_2_711

def word864_4_503 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_501 word864_2_713

def word864_4_507 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_503 word864_2_717

def word864_4_509 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_507 word864_3_508

def word864_4_516 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 1677 (Flapjack.WordRegImm.reg 1681) word864_4_509 word864_3_515

def word864_4_517 : WordLangProgHOL (BitVec 64) :=
.seq word864_2_624 word864_4_516

def word864_4_518 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_517 word864_0_10

def word864_4_520 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_518 word864_2_744

def word864_4_521 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))))))
    Flapjack.Spt.ln)) word864_4_520 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)))
    Flapjack.Spt.ln))

def word864_4_522 : WordLangProgHOL (BitVec 64) :=
.seq word864_2_620 word864_4_521

def word864_4_523 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_437 word864_4_522

def word864_4_524 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_523 word864_0_10

def word864_4_532 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_524 word864_2_756

def word864_4_536 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_532 word864_2_760

def word864_4_538 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_536 word864_2_762

def word864_4_542 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_538 word864_2_766

def word864_4_544 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_542 word864_2_768

def word864_4_556 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_544 word864_3_555

def word864_4_557 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_556 word864_0_10

def word864_4_567 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_557 word864_3_566

def word864_4_568 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_567 word864_0_10

def word864_4_588 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_568 word864_3_587

def word864_4_589 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_588 word864_0_10

def word864_4_599 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_589 word864_2_864

def word864_4_611 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_599 word864_3_610

def word864_4_612 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_611 word864_0_10

def word864_4_614 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_612 word864_2_896

def word864_4_632 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_614 word864_3_631

def word864_4_633 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_632 word864_0_10

def word864_4_635 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_633 word864_2_926

def word864_4_647 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_635 word864_3_646

def word864_4_648 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_647 word864_0_10

def word864_4_650 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_648 word864_2_958

def word864_4_668 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_650 word864_3_667

def word864_4_669 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_668 word864_0_10

def word864_4_671 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_669 word864_2_988

def word864_4_673 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_671 word864_2_990

def word864_4_675 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_673 word864_2_992

def word864_4_687 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_675 word864_3_686

def word864_4_688 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_687 word864_0_10

def word864_4_690 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_688 word864_2_1024

def word864_4_708 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_690 word864_3_707

def word864_4_709 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_708 word864_0_10

def word864_4_711 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_709 word864_2_1054

def word864_4_713 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_711 word864_2_1056

def word864_4_715 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_713 word864_2_1058

def word864_4_727 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_715 word864_3_726

def word864_4_728 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_727 word864_0_10

def word864_4_730 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_728 word864_2_1090

def word864_4_748 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_730 word864_3_747

def word864_4_749 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_748 word864_0_10

def word864_4_759 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_749 word864_2_1128

def word864_4_761 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_759 word864_2_1130

def word864_4_773 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_761 word864_3_772

def word864_4_774 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_773 word864_0_10

def word864_4_776 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_774 word864_2_1162

def word864_4_794 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_776 word864_3_793

def word864_4_795 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_794 word864_0_10

def word864_4_803 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_795 word864_2_1198

def word864_4_807 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_803 word864_2_1202

def word864_4_809 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_807 word864_2_1204

def word864_4_821 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_809 word864_3_820

def word864_4_822 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_821 word864_0_10

def word864_4_824 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_822 word864_2_1236

def word864_4_842 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_824 word864_3_841

def word864_4_843 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_842 word864_0_10

def word864_4_853 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_843 word864_2_1274

def word864_4_854 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3565, 3545)]

def word864_4_855 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3569, 3549)]

def word864_4_856 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_854 word864_4_855

def word864_4_857 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3573, 3553)]

def word864_4_858 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_856 word864_4_857

def word864_4_859 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3577, 3557)]

def word864_4_860 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_858 word864_4_859

def word864_4_862 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_860 word864_2_1283

def word864_4_863 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_853 word864_4_862

def word864_4_865 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_863 word864_2_1286

def word864_4_877 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_865 word864_3_876

def word864_4_878 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_877 word864_0_10

def word864_4_880 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_878 word864_2_1318

def word864_4_898 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_880 word864_3_897

def word864_4_899 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_898 word864_0_10

def word864_4_901 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_899 word864_2_1348

def word864_4_903 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_901 word864_2_1350

def word864_4_905 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_903 word864_2_1352

def word864_4_917 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_905 word864_3_916

def word864_4_918 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_917 word864_0_10

def word864_4_928 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_918 word864_2_1390

def word864_4_929 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3921, 3901)]

def word864_4_930 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3925, 3905)]

def word864_4_931 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_929 word864_4_930

def word864_4_932 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3929, 3909)]

def word864_4_933 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_931 word864_4_932

def word864_4_934 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3933, 3913)]

def word864_4_935 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_933 word864_4_934

def word864_4_937 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_935 word864_2_1399

def word864_4_938 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_928 word864_4_937

def word864_4_956 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_938 word864_3_955

def word864_4_957 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_956 word864_0_10

def word864_4_959 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_957 word864_2_1430

def word864_4_963 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_959 word864_2_1434

def word864_4_978 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_963 word864_3_977

def word864_4_979 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_978 word864_0_10

def word864_4_981 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_979 word864_2_1469

def word864_4_985 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_981 word864_2_1473

def word864_4_987 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_985 word864_2_1477

def word864_4_1005 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_987 word864_3_1004

def word864_4_1006 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1005 word864_0_10

def word864_4_1008 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1006 word864_2_1507

def word864_4_1010 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1008 word864_2_1509

def word864_4_1024 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1010 word864_3_1023

def word864_4_1025 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1024 word864_0_10

def word864_4_1027 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1025 word864_2_1548

def word864_4_1031 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1027 word864_2_1552

def word864_4_1033 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1031 word864_2_1556

def word864_4_1051 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1033 word864_3_1050

def word864_4_1052 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1051 word864_0_10

def word864_4_1054 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1052 word864_2_1586

def word864_4_1056 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1054 word864_2_1588

def word864_4_1070 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1056 word864_3_1069

def word864_4_1071 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1070 word864_0_10

def word864_4_1073 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1071 word864_2_1627

def word864_4_1077 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1073 word864_2_1631

def word864_4_1079 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1077 word864_2_1635

def word864_4_1097 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1079 word864_3_1096

def word864_4_1098 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1097 word864_0_10

def word864_4_1100 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1098 word864_2_1665

def word864_4_1102 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1100 word864_2_1667

def word864_4_1116 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1102 word864_3_1115

def word864_4_1117 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1116 word864_0_10

def word864_4_1119 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1117 word864_2_1706

def word864_4_1123 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1119 word864_2_1710

def word864_4_1125 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1123 word864_2_1714

def word864_4_1143 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1125 word864_3_1142

def word864_4_1144 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1143 word864_0_10

def word864_4_1146 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1144 word864_2_1744

def word864_4_1148 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1146 word864_2_1746

def word864_4_1162 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1148 word864_3_1161

def word864_4_1163 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1162 word864_0_10

def word864_4_1165 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1163 word864_2_1785

def word864_4_1169 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1165 word864_2_1789

def word864_4_1171 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1169 word864_2_1793

def word864_4_1189 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1171 word864_3_1188

def word864_4_1190 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1189 word864_0_10

def word864_4_1192 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1190 word864_2_1823

def word864_4_1194 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1192 word864_2_1825

def word864_4_1208 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1194 word864_3_1207

def word864_4_1209 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1208 word864_0_10

def word864_4_1219 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1209 word864_2_1872

def word864_4_1223 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1219 word864_2_1876

def word864_4_1237 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1223 word864_3_1236

def word864_4_1238 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1237 word864_0_10

def word864_4_1240 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1238 word864_2_1907

def word864_4_1244 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1240 word864_2_1911

def word864_4_1246 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1244 word864_2_1915

def word864_4_1264 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1246 word864_3_1263

def word864_4_1265 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1264 word864_0_10

def word864_4_1267 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1265 word864_2_1945

def word864_4_1269 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1267 word864_2_1947

def word864_4_1283 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1269 word864_3_1282

def word864_4_1284 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1283 word864_0_10

def word864_4_1286 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1284 word864_2_1986

def word864_4_1290 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1286 word864_2_1990

def word864_4_1292 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1290 word864_2_1994

def word864_4_1310 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1292 word864_3_1309

def word864_4_1311 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1310 word864_0_10

def word864_4_1313 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1311 word864_2_2024

def word864_4_1315 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1313 word864_2_2026

def word864_4_1329 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1315 word864_3_1328

def word864_4_1330 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1329 word864_0_10

def word864_4_1332 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1330 word864_2_2065

def word864_4_1336 : WordLangProgHOL (BitVec 64) :=
.seq word864_4_1332 word864_2_2069

def word864_4_1337 : WordLangProgHOL (BitVec 64) :=
.seq word864_2_0 word864_4_1336

def pass864_4 : WordLangProgHOL (BitVec 64) :=
word864_4_1337
theorem pass864_4_eq : WordCse.wordCommonSubexpElim (pass864_3) = pass864_4 := by
  kernel_rfl
#print axioms pass864_4_eq
end InitECandidate.Proofs.WordStages
