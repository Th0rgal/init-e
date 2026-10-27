import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass345_4
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word345_5_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(437, 285)]

def word345_5_132 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_130 word345_2_214

def word345_5_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(445, 305)]

def word345_5_135 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_133 word345_2_217

def word345_5_136 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_132 word345_5_135

def word345_5_162 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_136 word345_3_161

def word345_5_163 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_162 word345_0_4

def word345_5_165 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_163 word345_2_260

def word345_5_167 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_165 word345_2_262

def word345_5_169 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_167 word345_2_264

def word345_5_177 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_169 word345_3_176

def word345_5_178 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_177 word345_0_4

def word345_5_180 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_178 word345_2_285

def word345_5_182 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_180 word345_2_287

def word345_5_190 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_182 word345_3_189

def word345_5_191 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_190 word345_0_4

def word345_5_193 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_191 word345_2_308

def word345_5_195 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_193 word345_2_310

def word345_5_203 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_195 word345_3_202

def word345_5_204 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_203 word345_0_4

def word345_5_206 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_204 word345_2_331

def word345_5_208 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_206 word345_2_333

def word345_5_216 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_208 word345_3_215

def word345_5_217 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_216 word345_0_4

def word345_5_219 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_217 word345_3_218

def word345_5_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(829, 285)]

def word345_5_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(833, 305)]

def word345_5_268 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_266 word345_5_267

def word345_5_294 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_268 word345_3_293

def word345_5_295 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_294 word345_0_4

def word345_5_296 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_265 word345_5_295

def word345_5_297 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_254 word345_5_296

def word345_5_298 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_297 word345_0_4

def word345_5_300 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_298 word345_3_299

def word345_5_301 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 433 (Flapjack.WordRegImm.imm 0#64) word345_5_219 word345_5_300

def word345_5_302 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_129 word345_5_301

def word345_5_303 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_302 word345_0_4

def word345_5_305 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_303 word345_2_509

def word345_5_307 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_305 word345_2_511

def word345_5_309 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_307 word345_2_513

def word345_5_313 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_309 word345_2_517

def word345_5_315 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_313 word345_2_519

def word345_5_317 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_315 word345_2_521

def word345_5_331 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_317 word345_3_330

def word345_5_332 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_331 word345_0_4

def word345_5_334 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_332 word345_2_552

def word345_5_336 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_334 word345_2_554

def word345_5_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(1043, 945), (1047, 929), (1051, 977), (1055, 973)]

def word345_5_357 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_337 word345_3_356

def word345_5_358 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_336 word345_5_357

def word345_5_359 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_358 word345_0_4

def word345_5_361 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_359 word345_2_588

def word345_5_363 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_361 word345_2_590

def word345_5_365 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_363 word345_2_592

def word345_5_379 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_365 word345_3_378

def word345_5_380 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_379 word345_0_4

def word345_5_382 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_380 word345_2_635

def word345_5_384 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_382 word345_2_637

def word345_5_386 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_384 word345_2_639

def word345_5_433 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_386 word345_3_432

def word345_5_434 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_433 word345_0_4

def word345_5_436 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_434 word345_2_736

def word345_5_438 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_436 word345_2_738

def word345_5_516 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_438 word345_3_515

def word345_5_517 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_516 word345_0_4

def word345_5_521 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_517 word345_2_865

def word345_5_523 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_521 word345_2_867

def word345_5_525 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_523 word345_2_869

def word345_5_527 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_525 word345_2_871

def word345_5_529 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_527 word345_2_873

def word345_5_531 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_529 word345_2_875

def word345_5_535 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_531 word345_2_879

def word345_5_537 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_535 word345_2_881

def word345_5_541 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_537 word345_2_885

def word345_5_543 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_541 word345_2_887

def word345_5_547 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_543 word345_2_891

def word345_5_549 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_547 word345_2_893

def word345_5_553 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_549 word345_2_897

def word345_5_557 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_553 word345_2_901

def word345_5_559 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_557 word345_2_903

def word345_5_561 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_559 word345_2_905

def word345_5_563 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_561 word345_2_907

def word345_5_802 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_563 word345_3_801

def word345_5_803 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_802 word345_0_4

def word345_5_805 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_803 word345_2_1198

def word345_5_807 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_805 word345_2_1200

def word345_5_809 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_807 word345_2_1206

def word345_5_811 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_809 word345_2_1208

def word345_5_829 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_811 word345_3_828

def word345_5_830 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_829 word345_0_4

def word345_5_834 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_830 word345_2_1240

def word345_5_836 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_834 word345_2_1242

def word345_5_838 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_836 word345_2_1244

def word345_5_842 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_838 word345_2_1248

def word345_5_846 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_842 word345_2_1252

def word345_5_848 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_846 word345_2_1254

def word345_5_850 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_848 word345_2_1256

def word345_5_852 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_850 word345_2_1258

def word345_5_906 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_852 word345_3_905

def word345_5_907 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_906 word345_0_4

def word345_5_911 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_907 word345_2_1349

def word345_5_913 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_911 word345_2_1351

def word345_5_915 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_913 word345_2_1353

def word345_5_919 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_915 word345_2_1357

def word345_5_923 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_919 word345_2_1361

def word345_5_925 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_923 word345_2_1363

def word345_5_927 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_925 word345_2_1365

def word345_5_929 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_927 word345_2_1367

def word345_5_931 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_929 word345_2_1371

def word345_5_961 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_931 word345_3_960

def word345_5_962 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_961 word345_0_4

def word345_5_966 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_962 word345_2_1415

def word345_5_968 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_966 word345_2_1417

def word345_5_970 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_968 word345_2_1419

def word345_5_972 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_970 word345_2_1421

def word345_5_974 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_972 word345_2_1423

def word345_5_976 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_974 word345_2_1425

def word345_5_980 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_976 word345_2_1429

def word345_5_982 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_980 word345_2_1431

def word345_5_986 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_982 word345_2_1435

def word345_5_988 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_986 word345_2_1437

def word345_5_992 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_988 word345_2_1441

def word345_5_994 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_992 word345_2_1443

def word345_5_998 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_994 word345_2_1447

def word345_5_1002 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_998 word345_2_1451

def word345_5_1004 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1002 word345_2_1453

def word345_5_1006 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1004 word345_2_1455

def word345_5_1008 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1006 word345_2_1457

def word345_5_1030 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1008 word345_3_1029

def word345_5_1031 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1030 word345_0_4

def word345_5_1035 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1031 word345_2_1493

def word345_5_1037 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1035 word345_2_1495

def word345_5_1039 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1037 word345_2_1497

def word345_5_1043 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1039 word345_2_1501

def word345_5_1047 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1043 word345_2_1505

def word345_5_1049 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1047 word345_2_1507

def word345_5_1051 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1049 word345_2_1509

def word345_5_1055 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1051 word345_2_1513

def word345_5_1059 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1055 word345_2_1517

def word345_5_1061 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1059 word345_2_1519

def word345_5_1063 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1061 word345_2_1521

def word345_5_1065 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1063 word345_2_1523

def word345_5_1155 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1065 word345_3_1154

def word345_5_1156 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1155 word345_0_4

def word345_5_1158 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1156 word345_2_1672

def word345_5_1160 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1158 word345_2_1674

def word345_5_1325 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1160 word345_3_1324

def word345_5_1326 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1325 word345_0_4

def word345_5_1328 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1326 word345_2_1899

def word345_5_1330 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1328 word345_2_1901

def word345_5_1420 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1330 word345_3_1419

def word345_5_1421 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1420 word345_0_4

def word345_5_1423 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1421 word345_2_2042

def word345_5_1425 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1423 word345_2_2044

def word345_5_1457 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1425 word345_3_1456

def word345_5_1458 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1457 word345_0_4

def word345_5_1462 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1458 word345_2_2092

def word345_5_1464 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1462 word345_2_2094

def word345_5_1466 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1464 word345_2_2096

def word345_5_1468 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1466 word345_2_2098

def word345_5_1470 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1468 word345_2_2100

def word345_5_1472 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1470 word345_2_2102

def word345_5_1476 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1472 word345_2_2106

def word345_5_1478 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1476 word345_2_2108

def word345_5_1482 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1478 word345_2_2112

def word345_5_1484 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1482 word345_2_2114

def word345_5_1488 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1484 word345_2_2118

def word345_5_1490 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1488 word345_2_2120

def word345_5_1494 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1490 word345_2_2124

def word345_5_1496 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1494 word345_2_2126

def word345_5_1500 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1496 word345_2_2130

def word345_5_1532 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1500 word345_3_1531

def word345_5_1533 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1532 word345_0_4

def word345_5_1537 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1533 word345_2_2178

def word345_5_1539 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1537 word345_2_2180

def word345_5_1541 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1539 word345_2_2182

def word345_5_1543 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1541 word345_2_2184

def word345_5_1545 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1543 word345_2_2186

def word345_5_1547 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1545 word345_2_2188

def word345_5_1551 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1547 word345_2_2192

def word345_5_1553 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1551 word345_2_2194

def word345_5_1557 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1553 word345_2_2198

def word345_5_1559 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1557 word345_2_2200

def word345_5_1563 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1559 word345_2_2204

def word345_5_1565 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1563 word345_2_2206

def word345_5_1569 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1565 word345_2_2210

def word345_5_1571 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1569 word345_2_2212

def word345_5_1575 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1571 word345_2_2216

def word345_5_1607 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1575 word345_3_1606

def word345_5_1608 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1607 word345_0_4

def word345_5_1612 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1608 word345_2_2264

def word345_5_1614 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1612 word345_2_2266

def word345_5_1616 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1614 word345_2_2268

def word345_5_1618 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1616 word345_2_2270

def word345_5_1620 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1618 word345_2_2272

def word345_5_1622 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1620 word345_2_2274

def word345_5_1626 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1622 word345_2_2278

def word345_5_1628 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1626 word345_2_2280

def word345_5_1632 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1628 word345_2_2284

def word345_5_1634 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1632 word345_2_2286

def word345_5_1638 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1634 word345_2_2290

def word345_5_1640 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1638 word345_2_2292

def word345_5_1644 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1640 word345_2_2296

def word345_5_1646 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1644 word345_2_2298

def word345_5_1650 : WordLangProgHOL (BitVec 64) :=
.seq word345_5_1646 word345_2_2302

def word345_5_1651 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_0 word345_5_1650

def pass345_5 : WordLangProgHOL (BitVec 64) :=
word345_5_1651
theorem pass345_5_eq : WordCopy.copyProp (pass345_4) = pass345_5 := by
  kernel_rfl
#print axioms pass345_5_eq
end InitECandidate.Proofs.WordStages
