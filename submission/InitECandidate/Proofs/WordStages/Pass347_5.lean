import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass347_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word347_5_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(437, 285)]

def word347_5_132 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_130 word347_2_214

def word347_5_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(445, 305)]

def word347_5_135 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_133 word347_2_217

def word347_5_136 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_132 word347_5_135

def word347_5_162 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_136 word347_4_161

def word347_5_163 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_162 word347_0_4

def word347_5_165 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_163 word347_2_260

def word347_5_167 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_165 word347_2_262

def word347_5_169 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_167 word347_2_264

def word347_5_177 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_169 word347_4_176

def word347_5_178 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_177 word347_0_4

def word347_5_180 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_178 word347_2_285

def word347_5_182 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_180 word347_2_287

def word347_5_190 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_182 word347_4_189

def word347_5_191 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_190 word347_0_4

def word347_5_193 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_191 word347_2_308

def word347_5_195 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_193 word347_2_310

def word347_5_203 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_195 word347_4_202

def word347_5_204 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_203 word347_0_4

def word347_5_206 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_204 word347_2_331

def word347_5_208 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_206 word347_2_333

def word347_5_216 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_208 word347_4_215

def word347_5_217 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_216 word347_0_4

def word347_5_219 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_217 word347_4_218

def word347_5_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(829, 285)]

def word347_5_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(833, 305)]

def word347_5_268 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_266 word347_5_267

def word347_5_294 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_268 word347_4_293

def word347_5_295 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_294 word347_0_4

def word347_5_296 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_265 word347_5_295

def word347_5_297 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_254 word347_5_296

def word347_5_298 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_297 word347_0_4

def word347_5_300 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_298 word347_4_299

def word347_5_301 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 433 (Flapjack.WordRegImm.imm 0#64) word347_5_219 word347_5_300

def word347_5_302 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_129 word347_5_301

def word347_5_303 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_302 word347_0_4

def word347_5_305 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_303 word347_2_509

def word347_5_307 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_305 word347_2_511

def word347_5_309 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_307 word347_2_513

def word347_5_313 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_309 word347_2_517

def word347_5_315 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_313 word347_2_519

def word347_5_317 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_315 word347_2_521

def word347_5_331 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_317 word347_4_330

def word347_5_332 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_331 word347_0_4

def word347_5_334 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_332 word347_2_552

def word347_5_336 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_334 word347_2_554

def word347_5_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1043, 945), (1047, 929), (1051, 977), (1055, 973)]

def word347_5_357 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_337 word347_4_356

def word347_5_358 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_336 word347_5_357

def word347_5_359 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_358 word347_0_4

def word347_5_361 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_359 word347_2_588

def word347_5_363 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_361 word347_2_590

def word347_5_365 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_363 word347_2_592

def word347_5_379 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_365 word347_4_378

def word347_5_380 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_379 word347_0_4

def word347_5_382 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_380 word347_2_635

def word347_5_384 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_382 word347_2_637

def word347_5_386 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_384 word347_2_639

def word347_5_433 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_386 word347_4_432

def word347_5_434 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_433 word347_0_4

def word347_5_436 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_434 word347_2_736

def word347_5_438 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_436 word347_2_738

def word347_5_516 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_438 word347_4_515

def word347_5_517 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_516 word347_0_4

def word347_5_521 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_517 word347_2_865

def word347_5_523 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_521 word347_2_867

def word347_5_525 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_523 word347_2_869

def word347_5_527 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_525 word347_2_871

def word347_5_529 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_527 word347_2_873

def word347_5_531 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_529 word347_2_875

def word347_5_535 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_531 word347_2_879

def word347_5_537 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_535 word347_2_881

def word347_5_541 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_537 word347_2_885

def word347_5_543 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_541 word347_2_887

def word347_5_547 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_543 word347_2_891

def word347_5_549 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_547 word347_2_893

def word347_5_553 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_549 word347_2_897

def word347_5_557 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_553 word347_2_901

def word347_5_559 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_557 word347_2_903

def word347_5_561 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_559 word347_2_905

def word347_5_563 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_561 word347_2_907

def word347_5_802 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_563 word347_4_801

def word347_5_803 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_802 word347_0_4

def word347_5_805 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_803 word347_2_1198

def word347_5_807 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_805 word347_2_1200

def word347_5_809 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_807 word347_2_1206

def word347_5_811 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_809 word347_2_1208

def word347_5_829 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_811 word347_4_828

def word347_5_830 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_829 word347_0_4

def word347_5_834 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_830 word347_2_1240

def word347_5_836 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_834 word347_2_1242

def word347_5_838 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_836 word347_2_1244

def word347_5_842 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_838 word347_2_1248

def word347_5_846 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_842 word347_2_1252

def word347_5_848 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_846 word347_2_1254

def word347_5_850 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_848 word347_2_1256

def word347_5_852 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_850 word347_2_1258

def word347_5_906 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_852 word347_4_905

def word347_5_907 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_906 word347_0_4

def word347_5_911 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_907 word347_2_1349

def word347_5_913 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_911 word347_2_1351

def word347_5_915 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_913 word347_2_1353

def word347_5_919 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_915 word347_2_1357

def word347_5_923 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_919 word347_2_1361

def word347_5_925 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_923 word347_2_1363

def word347_5_927 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_925 word347_2_1365

def word347_5_929 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_927 word347_2_1367

def word347_5_931 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_929 word347_2_1371

def word347_5_961 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_931 word347_4_960

def word347_5_962 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_961 word347_0_4

def word347_5_966 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_962 word347_2_1415

def word347_5_968 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_966 word347_2_1417

def word347_5_970 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_968 word347_2_1419

def word347_5_972 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_970 word347_2_1421

def word347_5_974 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_972 word347_2_1423

def word347_5_976 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_974 word347_2_1425

def word347_5_980 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_976 word347_2_1429

def word347_5_982 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_980 word347_2_1431

def word347_5_986 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_982 word347_2_1435

def word347_5_988 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_986 word347_2_1437

def word347_5_992 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_988 word347_2_1441

def word347_5_994 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_992 word347_2_1443

def word347_5_998 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_994 word347_2_1447

def word347_5_1002 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_998 word347_2_1451

def word347_5_1004 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1002 word347_2_1453

def word347_5_1006 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1004 word347_2_1455

def word347_5_1008 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1006 word347_2_1457

def word347_5_1030 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1008 word347_4_1029

def word347_5_1031 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1030 word347_0_4

def word347_5_1035 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1031 word347_2_1493

def word347_5_1037 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1035 word347_2_1495

def word347_5_1039 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1037 word347_2_1497

def word347_5_1043 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1039 word347_2_1501

def word347_5_1047 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1043 word347_2_1505

def word347_5_1049 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1047 word347_2_1507

def word347_5_1051 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1049 word347_2_1509

def word347_5_1055 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1051 word347_2_1513

def word347_5_1059 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1055 word347_2_1517

def word347_5_1061 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1059 word347_2_1519

def word347_5_1063 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1061 word347_2_1521

def word347_5_1065 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1063 word347_2_1523

def word347_5_1155 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1065 word347_4_1154

def word347_5_1156 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1155 word347_0_4

def word347_5_1158 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1156 word347_2_1672

def word347_5_1160 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1158 word347_2_1674

def word347_5_1325 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1160 word347_4_1324

def word347_5_1326 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1325 word347_0_4

def word347_5_1328 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1326 word347_2_1899

def word347_5_1330 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1328 word347_2_1901

def word347_5_1420 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1330 word347_4_1419

def word347_5_1421 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1420 word347_0_4

def word347_5_1423 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1421 word347_2_2042

def word347_5_1425 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1423 word347_2_2044

def word347_5_1457 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1425 word347_4_1456

def word347_5_1458 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1457 word347_0_4

def word347_5_1462 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1458 word347_2_2092

def word347_5_1464 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1462 word347_2_2094

def word347_5_1466 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1464 word347_2_2096

def word347_5_1468 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1466 word347_2_2098

def word347_5_1470 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1468 word347_2_2100

def word347_5_1472 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1470 word347_2_2102

def word347_5_1476 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1472 word347_2_2106

def word347_5_1478 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1476 word347_2_2108

def word347_5_1482 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1478 word347_2_2112

def word347_5_1484 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1482 word347_2_2114

def word347_5_1488 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1484 word347_2_2118

def word347_5_1490 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1488 word347_2_2120

def word347_5_1494 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1490 word347_2_2124

def word347_5_1496 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1494 word347_2_2126

def word347_5_1500 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1496 word347_2_2130

def word347_5_1532 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1500 word347_4_1531

def word347_5_1533 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1532 word347_0_4

def word347_5_1537 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1533 word347_2_2178

def word347_5_1539 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1537 word347_2_2180

def word347_5_1541 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1539 word347_2_2182

def word347_5_1543 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1541 word347_2_2184

def word347_5_1545 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1543 word347_2_2186

def word347_5_1547 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1545 word347_2_2188

def word347_5_1551 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1547 word347_2_2192

def word347_5_1553 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1551 word347_2_2194

def word347_5_1557 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1553 word347_2_2198

def word347_5_1559 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1557 word347_2_2200

def word347_5_1563 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1559 word347_2_2204

def word347_5_1565 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1563 word347_2_2206

def word347_5_1569 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1565 word347_2_2210

def word347_5_1571 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1569 word347_2_2212

def word347_5_1575 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1571 word347_2_2216

def word347_5_1607 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1575 word347_4_1606

def word347_5_1608 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1607 word347_0_4

def word347_5_1612 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1608 word347_2_2264

def word347_5_1614 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1612 word347_2_2266

def word347_5_1616 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1614 word347_2_2268

def word347_5_1618 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1616 word347_2_2270

def word347_5_1620 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1618 word347_2_2272

def word347_5_1622 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1620 word347_2_2274

def word347_5_1626 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1622 word347_2_2278

def word347_5_1628 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1626 word347_2_2280

def word347_5_1632 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1628 word347_2_2284

def word347_5_1634 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1632 word347_2_2286

def word347_5_1638 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1634 word347_2_2290

def word347_5_1640 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1638 word347_2_2292

def word347_5_1644 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1640 word347_2_2296

def word347_5_1646 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1644 word347_2_2298

def word347_5_1650 : WordLangProgHOL (BitVec 64) :=
.seq word347_5_1646 word347_2_2302

def word347_5_1651 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_0 word347_5_1650

def pass347_5 : WordLangProgHOL (BitVec 64) :=
word347_5_1651
theorem pass347_5_eq : WordCopy.copyProp (pass347_4) = pass347_5 := by
  kernel_rfl
#print axioms pass347_5_eq
end InitECandidate.Proofs.WordStages
