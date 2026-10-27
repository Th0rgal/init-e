import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass868_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word868_5_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(387, 305), (391, 309), (395, 365), (399, 373), (403, 317), (407, 321)]

def word868_5_135 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_119 word868_3_134

def word868_5_136 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_118 word868_5_135

def word868_5_137 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_136 word868_0_10

def word868_5_147 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_137 word868_2_194

def word868_5_149 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_147 word868_2_196

def word868_5_151 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_149 word868_2_198

def word868_5_155 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_151 word868_2_202

def word868_5_157 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_155 word868_2_208

def word868_5_159 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_157 word868_2_210

def word868_5_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(503, 413), (507, 477), (511, 417), (515, 421), (519, 425), (523, 429), (527, 433)]

def word868_5_176 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_160 word868_3_175

def word868_5_177 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_159 word868_5_176

def word868_5_178 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_177 word868_0_10

def word868_5_188 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_178 word868_2_248

def word868_5_190 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_188 word868_2_250

def word868_5_192 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_190 word868_2_252

def word868_5_196 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_192 word868_2_256

def word868_5_198 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_196 word868_2_260

def word868_5_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(619, 533), (623, 537), (627, 541), (631, 545), (635, 549), (639, 553), (643, 601), (647, 557)]

def word868_5_215 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_199 word868_3_214

def word868_5_216 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_198 word868_5_215

def word868_5_217 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_216 word868_0_10

def word868_5_227 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_217 word868_2_298

def word868_5_229 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_227 word868_2_300

def word868_5_231 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_229 word868_2_302

def word868_5_235 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_231 word868_2_306

def word868_5_237 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_235 word868_2_312

def word868_5_239 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_237 word868_2_314

def word868_5_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(751, 653), (755, 725), (759, 657), (763, 661), (767, 665), (771, 669), (775, 673), (779, 677), (783, 681)]

def word868_5_256 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_240 word868_3_255

def word868_5_257 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_239 word868_5_256

def word868_5_258 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_257 word868_0_10

def word868_5_268 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_258 word868_2_352

def word868_5_270 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_268 word868_2_354

def word868_5_272 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_270 word868_2_356

def word868_5_276 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_272 word868_2_360

def word868_5_286 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_276 word868_4_285

def word868_5_288 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_286 word868_2_372

def word868_5_290 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_288 word868_2_374

def word868_5_294 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_290 word868_2_378

def word868_5_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0
  [(907, 789), (911, 865), (915, 793), (919, 797), (923, 801), (927, 805), (931, 897), (935, 813), (939, 817),
    (943, 821)]

def word868_5_303 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_295 word868_3_302

def word868_5_304 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_294 word868_5_303

def word868_5_305 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_304 word868_0_10

def word868_5_313 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_305 word868_2_413

def word868_5_317 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_313 word868_2_417

def word868_5_319 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_317 word868_2_421

def word868_5_331 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_319 word868_3_330

def word868_5_332 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_331 word868_0_10

def word868_5_340 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_332 word868_2_457

def word868_5_342 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_340 word868_2_459

def word868_5_350 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_342 word868_4_349

def word868_5_378 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_350 word868_4_377

def word868_5_379 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_378 word868_0_10

def word868_5_387 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_379 word868_4_386

def word868_5_389 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_387 word868_2_520

def word868_5_391 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_389 word868_2_524

def word868_5_403 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_391 word868_3_402

def word868_5_404 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_403 word868_0_10

def word868_5_414 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_404 word868_3_413

def word868_5_415 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_414 word868_0_10

def word868_5_417 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_415 word868_2_583

def word868_5_429 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_417 word868_3_428

def word868_5_430 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_429 word868_0_10

def word868_5_434 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_430 word868_2_615

def word868_5_436 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_434 word868_2_617

def word868_5_437 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_436 word868_0_10

def word868_5_508 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2065, 1625), (2061, 1629), (2057, 1633), (2053, 1637), (2049, 1641), (2045, 1645), (2041, 1649), (2037, 1653),
    (2033, 1657), (2025, 1661), (2021, 1665), (2017, 1669), (2009, 1673)]

def word868_5_509 : WordLangProgHOL (BitVec 64) :=
.seq word868_4_507 word868_5_508

def word868_5_514 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(2065, 1625), (2061, 1629), (2057, 1677), (2053, 1637), (2049, 1641), (2045, 1645), (2041, 1649), (2037, 1653),
    (2033, 1657), (2025, 1661), (2021, 1665), (2017, 1669), (2009, 1673)]

def word868_5_515 : WordLangProgHOL (BitVec 64) :=
.seq word868_3_513 word868_5_514

def word868_5_516 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 1677 (Flapjack.WordRegImm.reg 1681) word868_5_509 word868_5_515

def word868_5_517 : WordLangProgHOL (BitVec 64) :=
.seq word868_2_624 word868_5_516

def word868_5_518 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_517 word868_0_10

def word868_5_520 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_518 word868_2_744

def word868_5_521 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word868_5_520 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word868_5_522 : WordLangProgHOL (BitVec 64) :=
.seq word868_2_620 word868_5_521

def word868_5_523 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_437 word868_5_522

def word868_5_524 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_523 word868_0_10

def word868_5_532 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_524 word868_2_756

def word868_5_536 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_532 word868_2_760

def word868_5_538 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_536 word868_2_762

def word868_5_542 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_538 word868_2_766

def word868_5_544 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_542 word868_2_768

def word868_5_556 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_544 word868_3_555

def word868_5_557 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_556 word868_0_10

def word868_5_567 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_557 word868_3_566

def word868_5_568 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_567 word868_0_10

def word868_5_588 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_568 word868_3_587

def word868_5_589 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_588 word868_0_10

def word868_5_599 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_589 word868_2_864

def word868_5_611 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_599 word868_3_610

def word868_5_612 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_611 word868_0_10

def word868_5_614 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_612 word868_2_896

def word868_5_632 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_614 word868_3_631

def word868_5_633 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_632 word868_0_10

def word868_5_635 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_633 word868_2_926

def word868_5_647 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_635 word868_3_646

def word868_5_648 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_647 word868_0_10

def word868_5_650 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_648 word868_2_958

def word868_5_668 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_650 word868_3_667

def word868_5_669 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_668 word868_0_10

def word868_5_671 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_669 word868_2_988

def word868_5_673 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_671 word868_2_990

def word868_5_675 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_673 word868_2_992

def word868_5_687 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_675 word868_3_686

def word868_5_688 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_687 word868_0_10

def word868_5_690 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_688 word868_2_1024

def word868_5_708 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_690 word868_3_707

def word868_5_709 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_708 word868_0_10

def word868_5_711 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_709 word868_2_1054

def word868_5_713 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_711 word868_2_1056

def word868_5_715 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_713 word868_2_1058

def word868_5_727 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_715 word868_3_726

def word868_5_728 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_727 word868_0_10

def word868_5_730 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_728 word868_2_1090

def word868_5_748 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_730 word868_3_747

def word868_5_749 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_748 word868_0_10

def word868_5_759 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_749 word868_2_1128

def word868_5_761 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_759 word868_2_1130

def word868_5_773 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_761 word868_3_772

def word868_5_774 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_773 word868_0_10

def word868_5_776 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_774 word868_2_1162

def word868_5_794 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_776 word868_3_793

def word868_5_795 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_794 word868_0_10

def word868_5_803 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_795 word868_2_1198

def word868_5_807 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_803 word868_2_1202

def word868_5_809 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_807 word868_2_1204

def word868_5_821 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_809 word868_3_820

def word868_5_822 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_821 word868_0_10

def word868_5_824 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_822 word868_2_1236

def word868_5_842 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_824 word868_3_841

def word868_5_843 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_842 word868_0_10

def word868_5_853 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_843 word868_2_1274

def word868_5_863 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_853 word868_4_862

def word868_5_865 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_863 word868_2_1286

def word868_5_877 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_865 word868_3_876

def word868_5_878 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_877 word868_0_10

def word868_5_880 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_878 word868_2_1318

def word868_5_898 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_880 word868_3_897

def word868_5_899 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_898 word868_0_10

def word868_5_901 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_899 word868_2_1348

def word868_5_903 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_901 word868_2_1350

def word868_5_905 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_903 word868_2_1352

def word868_5_917 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_905 word868_3_916

def word868_5_918 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_917 word868_0_10

def word868_5_928 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_918 word868_2_1390

def word868_5_938 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_928 word868_4_937

def word868_5_956 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_938 word868_3_955

def word868_5_957 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_956 word868_0_10

def word868_5_959 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_957 word868_2_1430

def word868_5_963 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_959 word868_2_1434

def word868_5_978 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_963 word868_3_977

def word868_5_979 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_978 word868_0_10

def word868_5_981 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_979 word868_2_1469

def word868_5_985 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_981 word868_2_1473

def word868_5_987 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_985 word868_2_1477

def word868_5_1005 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_987 word868_3_1004

def word868_5_1006 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1005 word868_0_10

def word868_5_1008 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1006 word868_2_1507

def word868_5_1010 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1008 word868_2_1509

def word868_5_1024 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1010 word868_3_1023

def word868_5_1025 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1024 word868_0_10

def word868_5_1027 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1025 word868_2_1548

def word868_5_1031 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1027 word868_2_1552

def word868_5_1033 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1031 word868_2_1556

def word868_5_1051 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1033 word868_3_1050

def word868_5_1052 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1051 word868_0_10

def word868_5_1054 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1052 word868_2_1586

def word868_5_1056 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1054 word868_2_1588

def word868_5_1070 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1056 word868_3_1069

def word868_5_1071 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1070 word868_0_10

def word868_5_1073 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1071 word868_2_1627

def word868_5_1077 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1073 word868_2_1631

def word868_5_1079 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1077 word868_2_1635

def word868_5_1097 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1079 word868_3_1096

def word868_5_1098 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1097 word868_0_10

def word868_5_1100 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1098 word868_2_1665

def word868_5_1102 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1100 word868_2_1667

def word868_5_1116 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1102 word868_3_1115

def word868_5_1117 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1116 word868_0_10

def word868_5_1119 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1117 word868_2_1706

def word868_5_1123 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1119 word868_2_1710

def word868_5_1125 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1123 word868_2_1714

def word868_5_1143 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1125 word868_3_1142

def word868_5_1144 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1143 word868_0_10

def word868_5_1146 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1144 word868_2_1744

def word868_5_1148 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1146 word868_2_1746

def word868_5_1162 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1148 word868_3_1161

def word868_5_1163 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1162 word868_0_10

def word868_5_1165 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1163 word868_2_1785

def word868_5_1169 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1165 word868_2_1789

def word868_5_1171 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1169 word868_2_1793

def word868_5_1189 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1171 word868_3_1188

def word868_5_1190 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1189 word868_0_10

def word868_5_1192 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1190 word868_2_1823

def word868_5_1194 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1192 word868_2_1825

def word868_5_1208 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1194 word868_3_1207

def word868_5_1209 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1208 word868_0_10

def word868_5_1219 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1209 word868_2_1872

def word868_5_1223 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1219 word868_2_1876

def word868_5_1237 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1223 word868_3_1236

def word868_5_1238 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1237 word868_0_10

def word868_5_1240 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1238 word868_2_1907

def word868_5_1244 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1240 word868_2_1911

def word868_5_1246 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1244 word868_2_1915

def word868_5_1264 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1246 word868_3_1263

def word868_5_1265 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1264 word868_0_10

def word868_5_1267 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1265 word868_2_1945

def word868_5_1269 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1267 word868_2_1947

def word868_5_1283 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1269 word868_3_1282

def word868_5_1284 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1283 word868_0_10

def word868_5_1286 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1284 word868_2_1986

def word868_5_1290 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1286 word868_2_1990

def word868_5_1292 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1290 word868_2_1994

def word868_5_1310 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1292 word868_3_1309

def word868_5_1311 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1310 word868_0_10

def word868_5_1313 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1311 word868_2_2024

def word868_5_1315 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1313 word868_2_2026

def word868_5_1329 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1315 word868_3_1328

def word868_5_1330 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1329 word868_0_10

def word868_5_1332 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1330 word868_2_2065

def word868_5_1336 : WordLangProgHOL (BitVec 64) :=
.seq word868_5_1332 word868_2_2069

def word868_5_1337 : WordLangProgHOL (BitVec 64) :=
.seq word868_2_0 word868_5_1336

def pass868_5 : WordLangProgHOL (BitVec 64) :=
word868_5_1337
theorem pass868_5_eq : WordCopy.copyProp (pass868_4) = pass868_5 := by
  kernel_rfl
#print axioms pass868_5_eq
end InitECandidate.Proofs.WordStages
