import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof19
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1280_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2371 state64 453 state65 = (program38787,state13578,26045) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2371
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1278_eq, node1279_eq]
  kernel_rfl
theorem node1281_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2377 state13578 26045 state65 = (program38796,state13599,26065) := by
  kernel_rfl
theorem node1282_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2378 state64 453 state65 = (program38797,state13599,26065) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2378
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1280_eq, node1281_eq]
  kernel_rfl
theorem node1283_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2379 state13599 26065 state65 = (program38798,state13608,26069) := by
  kernel_rfl
theorem node1284_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2380 state64 453 state65 = (program38799,state13608,26069) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2380
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1282_eq, node1283_eq]
  kernel_rfl
theorem node1285_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2386 state13608 26069 state65 = (program38808,state13628,26089) := by
  kernel_rfl
theorem node1286_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2387 state64 453 state65 = (program38809,state13628,26089) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2387
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1284_eq, node1285_eq]
  kernel_rfl
theorem node1287_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2388 state13628 26089 state65 = (program38810,state13637,26093) := by
  kernel_rfl
theorem node1288_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2389 state64 453 state65 = (program38811,state13637,26093) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2389
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1286_eq, node1287_eq]
  kernel_rfl
theorem node1289_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2395 state13637 26093 state65 = (program38820,state13660,26113) := by
  kernel_rfl
theorem node1290_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2396 state64 453 state65 = (program38821,state13660,26113) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2396
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1288_eq, node1289_eq]
  kernel_rfl
theorem node1291_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2397 state13660 26113 state65 = (program38822,state13670,26117) := by
  kernel_rfl
theorem node1292_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2398 state64 453 state65 = (program38823,state13670,26117) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2398
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1290_eq, node1291_eq]
  kernel_rfl
theorem node1293_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2404 state13670 26117 state65 = (program38832,state13696,26137) := by
  kernel_rfl
theorem node1294_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2405 state64 453 state65 = (program38833,state13696,26137) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2405
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1292_eq, node1293_eq]
  kernel_rfl
theorem node1295_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2406 state13696 26137 state65 = (program38834,state13708,26141) := by
  kernel_rfl
theorem node1296_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2407 state64 453 state65 = (program38835,state13708,26141) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2407
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1294_eq, node1295_eq]
  kernel_rfl
theorem node1297_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2415 state13708 26141 state65 = (program38889,state13750,26257) := by
  kernel_rfl
theorem node1298_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2416 state64 453 state65 = (program38890,state13750,26257) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2416
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1296_eq, node1297_eq]
  kernel_rfl
theorem node1299_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state13750 26257 state65 = (program38899,state13776,26277) := by
  kernel_rfl
theorem node1300_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2417 state64 453 state65 = (program38900,state13776,26277) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2417
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1298_eq, node1299_eq]
  kernel_rfl
theorem node1301_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state13776 26277 state65 = (program38901,state13789,26281) := by
  kernel_rfl
theorem node1302_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2418 state64 453 state65 = (program38902,state13789,26281) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2418
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1300_eq, node1301_eq]
  kernel_rfl
theorem node1303_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state13789 26281 state65 = (program38959,state13831,26405) := by
  kernel_rfl
theorem node1304_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2419 state64 453 state65 = (program38960,state13831,26405) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2419
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1302_eq, node1303_eq]
  kernel_rfl
theorem node1305_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2427 state13831 26405 state65 = (program39014,state13871,26521) := by
  kernel_rfl
theorem node1306_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2428 state64 453 state65 = (program39015,state13871,26521) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2428
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1304_eq, node1305_eq]
  kernel_rfl
theorem node1307_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state13871 26521 state65 = (program39024,state13897,26541) := by
  kernel_rfl
theorem node1308_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2429 state64 453 state65 = (program39025,state13897,26541) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2429
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1306_eq, node1307_eq]
  kernel_rfl
theorem node1309_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state13897 26541 state65 = (program39026,state13910,26545) := by
  kernel_rfl
theorem node1310_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2430 state64 453 state65 = (program39027,state13910,26545) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2430
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1308_eq, node1309_eq]
  kernel_rfl
theorem node1311_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state13910 26545 state65 = (program39084,state13953,26669) := by
  kernel_rfl
theorem node1312_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2431 state64 453 state65 = (program39085,state13953,26669) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2431
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1310_eq, node1311_eq]
  kernel_rfl
theorem node1313_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2439 state13953 26669 state65 = (program39139,state13994,26785) := by
  kernel_rfl
theorem node1314_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2440 state64 453 state65 = (program39140,state13994,26785) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2440
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1312_eq, node1313_eq]
  kernel_rfl
theorem node1315_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state13994 26785 state65 = (program39149,state14017,26805) := by
  kernel_rfl
theorem node1316_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2441 state64 453 state65 = (program39150,state14017,26805) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2441
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1314_eq, node1315_eq]
  kernel_rfl
theorem node1317_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state14017 26805 state65 = (program39151,state14029,26809) := by
  kernel_rfl
theorem node1318_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2442 state64 453 state65 = (program39152,state14029,26809) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2442
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1316_eq, node1317_eq]
  kernel_rfl
theorem node1319_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state14029 26809 state65 = (program39209,state14071,26933) := by
  kernel_rfl
theorem node1320_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2443 state64 453 state65 = (program39210,state14071,26933) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2443
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1318_eq, node1319_eq]
  kernel_rfl
theorem node1321_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2451 state14071 26933 state65 = (program39264,state14112,27049) := by
  kernel_rfl
theorem node1322_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2452 state64 453 state65 = (program39265,state14112,27049) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2452
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1320_eq, node1321_eq]
  kernel_rfl
theorem node1323_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state14112 27049 state65 = (program39274,state14135,27069) := by
  kernel_rfl
theorem node1324_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2453 state64 453 state65 = (program39275,state14135,27069) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2453
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1322_eq, node1323_eq]
  kernel_rfl
theorem node1325_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state14135 27069 state65 = (program39276,state14145,27073) := by
  kernel_rfl
theorem node1326_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2454 state64 453 state65 = (program39277,state14145,27073) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2454
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1324_eq, node1325_eq]
  kernel_rfl
theorem node1327_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state14145 27073 state65 = (program39334,state14187,27197) := by
  kernel_rfl
theorem node1328_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2455 state64 453 state65 = (program39335,state14187,27197) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2455
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1326_eq, node1327_eq]
  kernel_rfl
theorem node1329_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2461 state14187 27197 state65 = (program39389,state14229,27313) := by
  kernel_rfl
theorem node1330_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2462 state64 453 state65 = (program39390,state14229,27313) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2462
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1328_eq, node1329_eq]
  kernel_rfl
theorem node1331_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state14229 27313 state65 = (program39399,state14255,27333) := by
  kernel_rfl
theorem node1332_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2463 state64 453 state65 = (program39400,state14255,27333) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2463
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1330_eq, node1331_eq]
  kernel_rfl
theorem node1333_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state14255 27333 state65 = (program39401,state14268,27337) := by
  kernel_rfl
theorem node1334_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2464 state64 453 state65 = (program39402,state14268,27337) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2464
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1332_eq, node1333_eq]
  kernel_rfl
theorem node1335_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state14268 27337 state65 = (program39459,state14308,27461) := by
  kernel_rfl
theorem node1336_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2465 state64 453 state65 = (program39460,state14308,27461) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2465
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1334_eq, node1335_eq]
  kernel_rfl
theorem node1337_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2471 state14308 27461 state65 = (program39514,state14350,27577) := by
  kernel_rfl
theorem node1338_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2472 state64 453 state65 = (program39515,state14350,27577) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2472
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1336_eq, node1337_eq]
  kernel_rfl
theorem node1339_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state14350 27577 state65 = (program39524,state14376,27597) := by
  kernel_rfl
theorem node1340_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2473 state64 453 state65 = (program39525,state14376,27597) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2473
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1338_eq, node1339_eq]
  kernel_rfl
theorem node1341_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state14376 27597 state65 = (program39526,state14389,27601) := by
  kernel_rfl
theorem node1342_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2474 state64 453 state65 = (program39527,state14389,27601) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2474
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1340_eq, node1341_eq]
  kernel_rfl
theorem node1343_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state14389 27601 state65 = (program39584,state14430,27725) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
