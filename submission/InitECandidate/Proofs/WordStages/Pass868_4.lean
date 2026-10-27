import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass868_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word868_4_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(185, 157)]

def word868_4_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(189, 161)]

def word868_4_49 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_47 word868_4_48

def word868_4_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(193, 165)]

def word868_4_51 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_49 word868_4_50

def word868_4_53 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_51 word868_2_65

def word868_4_54 : WordLangProgHOL (BitVec 64) :=
.seq word868_3_46 word868_4_53

def word868_4_56 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_54 word868_2_70

def word868_4_68 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_56 word868_3_67

def word868_4_69 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_68 word868_0_10

def word868_4_75 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_69 word868_2_104

def word868_4_93 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_75 word868_3_92

def word868_4_94 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_93 word868_0_10

def word868_4_104 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_94 word868_2_142

def word868_4_106 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_104 word868_2_144

def word868_4_108 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_106 word868_2_146

def word868_4_112 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_108 word868_2_150

def word868_4_118 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_112 word868_2_156

def word868_4_136 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_118 word868_3_135

def word868_4_137 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_136 word868_0_10

def word868_4_147 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_137 word868_2_194

def word868_4_149 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_147 word868_2_196

def word868_4_151 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_149 word868_2_198

def word868_4_155 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_151 word868_2_202

def word868_4_157 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_155 word868_2_208

def word868_4_159 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_157 word868_2_210

def word868_4_177 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_159 word868_3_176

def word868_4_178 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_177 word868_0_10

def word868_4_188 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_178 word868_2_248

def word868_4_190 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_188 word868_2_250

def word868_4_192 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_190 word868_2_252

def word868_4_196 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_192 word868_2_256

def word868_4_198 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_196 word868_2_260

def word868_4_216 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_198 word868_3_215

def word868_4_217 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_216 word868_0_10

def word868_4_227 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_217 word868_2_298

def word868_4_229 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_227 word868_2_300

def word868_4_231 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_229 word868_2_302

def word868_4_235 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_231 word868_2_306

def word868_4_237 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_235 word868_2_312

def word868_4_239 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_237 word868_2_314

def word868_4_257 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_239 word868_3_256

def word868_4_258 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_257 word868_0_10

def word868_4_268 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_258 word868_2_352

def word868_4_270 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_268 word868_2_354

def word868_4_272 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_270 word868_2_356

def word868_4_276 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_272 word868_2_360

def word868_4_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(873, 841)]

def word868_4_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(877, 845)]

def word868_4_279 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_277 word868_4_278

def word868_4_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(881, 849)]

def word868_4_281 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_279 word868_4_280

def word868_4_283 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_281 word868_2_367

def word868_4_285 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_283 word868_2_369

def word868_4_286 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_276 word868_4_285

def word868_4_288 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_286 word868_2_372

def word868_4_290 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_288 word868_2_374

def word868_4_294 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_290 word868_2_378

def word868_4_304 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_294 word868_3_303

def word868_4_305 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_304 word868_0_10

def word868_4_313 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_305 word868_2_413

def word868_4_317 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_313 word868_2_417

def word868_4_319 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_317 word868_2_421

def word868_4_331 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_319 word868_3_330

def word868_4_332 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_331 word868_0_10

def word868_4_340 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_332 word868_2_457

def word868_4_342 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_340 word868_2_459

def word868_4_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1157, 1137)]

def word868_4_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1161, 1141)]

def word868_4_345 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_343 word868_4_344

def word868_4_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1165, 1145)]

def word868_4_347 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_345 word868_4_346

def word868_4_349 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_347 word868_2_466

def word868_4_350 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_342 word868_4_349

def word868_4_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1181, 1157)]

def word868_4_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1185, 1161)]

def word868_4_353 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_351 word868_4_352

def word868_4_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1189, 1165)]

def word868_4_355 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_353 word868_4_354

def word868_4_356 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1193, 1169)]

def word868_4_357 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_355 word868_4_356

def word868_4_359 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_357 word868_2_480

def word868_4_361 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_359 word868_2_482

def word868_4_362 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1205, 1181)]

def word868_4_363 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1209, 1185)]

def word868_4_364 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_362 word868_4_363

def word868_4_365 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1213, 1189)]

def word868_4_366 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_364 word868_4_365

def word868_4_368 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_366 word868_2_489

def word868_4_370 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_368 word868_2_491

def word868_4_371 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_361 word868_4_370

def word868_4_372 : WordLangProgHOL (BitVec 64) :=
.seq word868_0_10 word868_4_371

def word868_4_374 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_372 word868_3_373

def word868_4_377 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 1153 (Flapjack.WordRegImm.reg 1169) word868_4_374 word868_3_376

def word868_4_378 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_350 word868_4_377

def word868_4_379 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_378 word868_0_10

def word868_4_380 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1253, 1137)]

def word868_4_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1257, 1141)]

def word868_4_382 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_380 word868_4_381

def word868_4_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1261, 1145)]

def word868_4_384 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_382 word868_4_383

def word868_4_386 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_384 word868_2_517

def word868_4_387 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_379 word868_4_386

def word868_4_389 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_387 word868_2_520

def word868_4_391 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_389 word868_2_524

def word868_4_403 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_391 word868_3_402

def word868_4_404 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_403 word868_0_10

def word868_4_414 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_404 word868_3_413

def word868_4_415 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_414 word868_0_10

def word868_4_417 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_415 word868_2_583

def word868_4_429 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_417 word868_3_428

def word868_4_430 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_429 word868_0_10

def word868_4_434 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_430 word868_2_615

def word868_4_436 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_434 word868_2_617

def word868_4_437 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_436 word868_0_10

def word868_4_453 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1717, 1697)]

def word868_4_454 : WordLangProgHOL (BitVec 64) :=
.seq word868_2_639 word868_4_453

def word868_4_456 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1725, 1705)]

def word868_4_457 : WordLangProgHOL (BitVec 64) :=
.seq word868_2_642 word868_4_456

def word868_4_458 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_454 word868_4_457

def word868_4_460 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_458 word868_2_646

def word868_4_461 : WordLangProgHOL (BitVec 64) :=
.seq word868_3_451 word868_4_460

def word868_4_479 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_461 word868_3_478

def word868_4_480 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_479 word868_0_10

def word868_4_482 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_480 word868_2_677

def word868_4_484 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_482 word868_2_679

def word868_4_496 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_484 word868_3_495

def word868_4_497 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_496 word868_0_10

def word868_4_501 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_497 word868_2_711

def word868_4_503 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_501 word868_2_713

def word868_4_507 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_503 word868_2_717

def word868_4_509 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_507 word868_3_508

def word868_4_516 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 1677 (Flapjack.WordRegImm.reg 1681) word868_4_509 word868_3_515

def word868_4_517 : WordLangProgHOL (BitVec 64) :=
.seq word868_2_624 word868_4_516

def word868_4_518 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_517 word868_0_10

def word868_4_520 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_518 word868_2_744

def word868_4_521 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word868_4_520 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word868_4_522 : WordLangProgHOL (BitVec 64) :=
.seq word868_2_620 word868_4_521

def word868_4_523 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_437 word868_4_522

def word868_4_524 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_523 word868_0_10

def word868_4_532 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_524 word868_2_756

def word868_4_536 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_532 word868_2_760

def word868_4_538 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_536 word868_2_762

def word868_4_542 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_538 word868_2_766

def word868_4_544 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_542 word868_2_768

def word868_4_556 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_544 word868_3_555

def word868_4_557 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_556 word868_0_10

def word868_4_567 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_557 word868_3_566

def word868_4_568 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_567 word868_0_10

def word868_4_588 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_568 word868_3_587

def word868_4_589 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_588 word868_0_10

def word868_4_599 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_589 word868_2_864

def word868_4_611 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_599 word868_3_610

def word868_4_612 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_611 word868_0_10

def word868_4_614 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_612 word868_2_896

def word868_4_632 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_614 word868_3_631

def word868_4_633 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_632 word868_0_10

def word868_4_635 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_633 word868_2_926

def word868_4_647 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_635 word868_3_646

def word868_4_648 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_647 word868_0_10

def word868_4_650 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_648 word868_2_958

def word868_4_668 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_650 word868_3_667

def word868_4_669 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_668 word868_0_10

def word868_4_671 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_669 word868_2_988

def word868_4_673 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_671 word868_2_990

def word868_4_675 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_673 word868_2_992

def word868_4_687 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_675 word868_3_686

def word868_4_688 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_687 word868_0_10

def word868_4_690 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_688 word868_2_1024

def word868_4_708 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_690 word868_3_707

def word868_4_709 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_708 word868_0_10

def word868_4_711 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_709 word868_2_1054

def word868_4_713 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_711 word868_2_1056

def word868_4_715 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_713 word868_2_1058

def word868_4_727 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_715 word868_3_726

def word868_4_728 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_727 word868_0_10

def word868_4_730 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_728 word868_2_1090

def word868_4_748 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_730 word868_3_747

def word868_4_749 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_748 word868_0_10

def word868_4_759 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_749 word868_2_1128

def word868_4_761 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_759 word868_2_1130

def word868_4_773 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_761 word868_3_772

def word868_4_774 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_773 word868_0_10

def word868_4_776 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_774 word868_2_1162

def word868_4_794 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_776 word868_3_793

def word868_4_795 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_794 word868_0_10

def word868_4_803 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_795 word868_2_1198

def word868_4_807 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_803 word868_2_1202

def word868_4_809 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_807 word868_2_1204

def word868_4_821 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_809 word868_3_820

def word868_4_822 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_821 word868_0_10

def word868_4_824 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_822 word868_2_1236

def word868_4_842 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_824 word868_3_841

def word868_4_843 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_842 word868_0_10

def word868_4_853 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_843 word868_2_1274

def word868_4_854 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3565, 3545)]

def word868_4_855 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3569, 3549)]

def word868_4_856 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_854 word868_4_855

def word868_4_857 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3573, 3553)]

def word868_4_858 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_856 word868_4_857

def word868_4_859 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3577, 3557)]

def word868_4_860 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_858 word868_4_859

def word868_4_862 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_860 word868_2_1283

def word868_4_863 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_853 word868_4_862

def word868_4_865 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_863 word868_2_1286

def word868_4_877 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_865 word868_3_876

def word868_4_878 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_877 word868_0_10

def word868_4_880 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_878 word868_2_1318

def word868_4_898 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_880 word868_3_897

def word868_4_899 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_898 word868_0_10

def word868_4_901 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_899 word868_2_1348

def word868_4_903 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_901 word868_2_1350

def word868_4_905 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_903 word868_2_1352

def word868_4_917 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_905 word868_3_916

def word868_4_918 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_917 word868_0_10

def word868_4_928 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_918 word868_2_1390

def word868_4_929 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3921, 3901)]

def word868_4_930 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3925, 3905)]

def word868_4_931 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_929 word868_4_930

def word868_4_932 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3929, 3909)]

def word868_4_933 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_931 word868_4_932

def word868_4_934 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3933, 3913)]

def word868_4_935 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_933 word868_4_934

def word868_4_937 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_935 word868_2_1399

def word868_4_938 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_928 word868_4_937

def word868_4_956 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_938 word868_3_955

def word868_4_957 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_956 word868_0_10

def word868_4_959 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_957 word868_2_1430

def word868_4_963 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_959 word868_2_1434

def word868_4_978 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_963 word868_3_977

def word868_4_979 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_978 word868_0_10

def word868_4_981 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_979 word868_2_1469

def word868_4_985 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_981 word868_2_1473

def word868_4_987 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_985 word868_2_1477

def word868_4_1005 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_987 word868_3_1004

def word868_4_1006 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1005 word868_0_10

def word868_4_1008 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1006 word868_2_1507

def word868_4_1010 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1008 word868_2_1509

def word868_4_1024 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1010 word868_3_1023

def word868_4_1025 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1024 word868_0_10

def word868_4_1027 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1025 word868_2_1548

def word868_4_1031 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1027 word868_2_1552

def word868_4_1033 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1031 word868_2_1556

def word868_4_1051 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1033 word868_3_1050

def word868_4_1052 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1051 word868_0_10

def word868_4_1054 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1052 word868_2_1586

def word868_4_1056 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1054 word868_2_1588

def word868_4_1070 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1056 word868_3_1069

def word868_4_1071 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1070 word868_0_10

def word868_4_1073 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1071 word868_2_1627

def word868_4_1077 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1073 word868_2_1631

def word868_4_1079 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1077 word868_2_1635

def word868_4_1097 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1079 word868_3_1096

def word868_4_1098 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1097 word868_0_10

def word868_4_1100 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1098 word868_2_1665

def word868_4_1102 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1100 word868_2_1667

def word868_4_1116 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1102 word868_3_1115

def word868_4_1117 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1116 word868_0_10

def word868_4_1119 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1117 word868_2_1706

def word868_4_1123 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1119 word868_2_1710

def word868_4_1125 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1123 word868_2_1714

def word868_4_1143 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1125 word868_3_1142

def word868_4_1144 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1143 word868_0_10

def word868_4_1146 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1144 word868_2_1744

def word868_4_1148 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1146 word868_2_1746

def word868_4_1162 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1148 word868_3_1161

def word868_4_1163 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1162 word868_0_10

def word868_4_1165 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1163 word868_2_1785

def word868_4_1169 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1165 word868_2_1789

def word868_4_1171 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1169 word868_2_1793

def word868_4_1189 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1171 word868_3_1188

def word868_4_1190 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1189 word868_0_10

def word868_4_1192 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1190 word868_2_1823

def word868_4_1194 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1192 word868_2_1825

def word868_4_1208 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1194 word868_3_1207

def word868_4_1209 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1208 word868_0_10

def word868_4_1219 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1209 word868_2_1872

def word868_4_1223 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1219 word868_2_1876

def word868_4_1237 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1223 word868_3_1236

def word868_4_1238 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1237 word868_0_10

def word868_4_1240 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1238 word868_2_1907

def word868_4_1244 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1240 word868_2_1911

def word868_4_1246 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1244 word868_2_1915

def word868_4_1264 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1246 word868_3_1263

def word868_4_1265 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1264 word868_0_10

def word868_4_1267 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1265 word868_2_1945

def word868_4_1269 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1267 word868_2_1947

def word868_4_1283 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1269 word868_3_1282

def word868_4_1284 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1283 word868_0_10

def word868_4_1286 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1284 word868_2_1986

def word868_4_1290 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1286 word868_2_1990

def word868_4_1292 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1290 word868_2_1994

def word868_4_1310 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1292 word868_3_1309

def word868_4_1311 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1310 word868_0_10

def word868_4_1313 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1311 word868_2_2024

def word868_4_1315 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1313 word868_2_2026

def word868_4_1329 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1315 word868_3_1328

def word868_4_1330 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1329 word868_0_10

def word868_4_1332 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1330 word868_2_2065

def word868_4_1336 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_1332 word868_2_2069

def word868_4_1337 : WordLangProgHOL (BitVec 64) :=
.seq word868_2_0 word868_4_1336

def pass868_4 : WordLangProgHOL (BitVec 64) :=
word868_4_1337
theorem pass868_4_eq : WordCse.wordCommonSubexpElim (pass868_3) = pass868_4 := by
  kernel_rfl
#print axioms pass868_4_eq
end InitECandidate.Proofs.WordStages
