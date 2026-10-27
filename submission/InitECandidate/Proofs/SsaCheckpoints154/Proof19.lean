import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof18
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node1216_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state12898 24837 state65 = (program38187,state12906,24841) := by
  kernel_rfl
theorem node1217_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1959 state12832 24701 state65 = (program38188,state12906,24841) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1959
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1215_eq, node1216_eq]
  kernel_rfl
theorem node1218_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2317 state64 453 state65 = (program38189,state12906,24841) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2317
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1210_eq, node1217_eq]
  kernel_rfl
theorem node1219_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1961 state12906 24841 state65 = (program38190,state12919,24845) := by
  kernel_rfl
theorem node1220_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2318 state64 453 state65 = (program38191,state12919,24845) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2318
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1218_eq, node1219_eq]
  kernel_rfl
theorem node1221_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2321 state12919 24845 state65 = (program38252,state12963,24969) := by
  kernel_rfl
theorem node1222_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2322 state64 453 state65 = (program38253,state12963,24969) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2322
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1220_eq, node1221_eq]
  kernel_rfl
theorem node1223_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state12963 24969 state65 = (program38262,state12989,24989) := by
  kernel_rfl
theorem node1224_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2323 state64 453 state65 = (program38263,state12989,24989) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2323
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1222_eq, node1223_eq]
  kernel_rfl
theorem node1225_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state12989 24989 state65 = (program38264,state13002,24993) := by
  kernel_rfl
theorem node1226_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2324 state64 453 state65 = (program38265,state13002,24993) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2324
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1224_eq, node1225_eq]
  kernel_rfl
theorem node1227_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state13002 24993 state65 = (program38326,state13043,25117) := by
  kernel_rfl
theorem node1228_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2325 state64 453 state65 = (program38327,state13043,25117) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2325
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1226_eq, node1227_eq]
  kernel_rfl
theorem node1229_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1999 state13043 25117 state65 = (program38388,state13076,25241) := by
  kernel_rfl
theorem node1230_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1579 state13076 25241 state65 = (program38391,state13095,25249) := by
  kernel_rfl
theorem node1231_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2000 state13043 25117 state65 = (program38392,state13095,25249) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2000
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1229_eq, node1230_eq]
  kernel_rfl
theorem node1232_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state13095 25249 state65 = (program38393,state13103,25253) := by
  kernel_rfl
theorem node1233_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2001 state13043 25117 state65 = (program38394,state13103,25253) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2001
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1231_eq, node1232_eq]
  kernel_rfl
theorem node1234_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state13103 25253 state65 = (program38395,state13111,25257) := by
  kernel_rfl
theorem node1235_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2002 state13043 25117 state65 = (program38396,state13111,25257) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2002
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1233_eq, node1234_eq]
  kernel_rfl
theorem node1236_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2326 state64 453 state65 = (program38397,state13111,25257) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2326
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1228_eq, node1235_eq]
  kernel_rfl
theorem node1237_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2004 state13111 25257 state65 = (program38398,state13123,25261) := by
  kernel_rfl
theorem node1238_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2327 state64 453 state65 = (program38399,state13123,25261) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2327
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1236_eq, node1237_eq]
  kernel_rfl
theorem node1239_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2330 state13123 25261 state65 = (program38460,state13169,25385) := by
  kernel_rfl
theorem node1240_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2331 state64 453 state65 = (program38461,state13169,25385) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2331
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1238_eq, node1239_eq]
  kernel_rfl
theorem node1241_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state13169 25385 state65 = (program38470,state13193,25405) := by
  kernel_rfl
theorem node1242_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2332 state64 453 state65 = (program38471,state13193,25405) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2332
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1240_eq, node1241_eq]
  kernel_rfl
theorem node1243_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state13193 25405 state65 = (program38472,state13204,25409) := by
  kernel_rfl
theorem node1244_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2333 state64 453 state65 = (program38473,state13204,25409) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2333
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1242_eq, node1243_eq]
  kernel_rfl
theorem node1245_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state13204 25409 state65 = (program38534,state13245,25533) := by
  kernel_rfl
theorem node1246_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2334 state64 453 state65 = (program38535,state13245,25533) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2334
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1244_eq, node1245_eq]
  kernel_rfl
theorem node1247_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2042 state13245 25533 state65 = (program38596,state13276,25657) := by
  kernel_rfl
theorem node1248_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1626 state13276 25657 state65 = (program38599,state13296,25665) := by
  kernel_rfl
theorem node1249_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2043 state13245 25533 state65 = (program38600,state13296,25665) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2043
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1247_eq, node1248_eq]
  kernel_rfl
theorem node1250_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state13296 25665 state65 = (program38601,state13304,25669) := by
  kernel_rfl
theorem node1251_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2044 state13245 25533 state65 = (program38602,state13304,25669) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2044
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1249_eq, node1250_eq]
  kernel_rfl
theorem node1252_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state13304 25669 state65 = (program38603,state13312,25673) := by
  kernel_rfl
theorem node1253_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2045 state13245 25533 state65 = (program38604,state13312,25673) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2045
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1251_eq, node1252_eq]
  kernel_rfl
theorem node1254_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2335 state64 453 state65 = (program38605,state13312,25673) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2335
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1246_eq, node1253_eq]
  kernel_rfl
theorem node1255_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2047 state13312 25673 state65 = (program38606,state13325,25677) := by
  kernel_rfl
theorem node1256_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2336 state64 453 state65 = (program38607,state13325,25677) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2336
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1254_eq, node1255_eq]
  kernel_rfl
theorem node1257_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2339 state13325 25677 state65 = (program38667,state13370,25801) := by
  kernel_rfl
theorem node1258_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2340 state64 453 state65 = (program38668,state13370,25801) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2340
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1256_eq, node1257_eq]
  kernel_rfl
theorem node1259_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state13370 25801 state65 = (program38676,state13392,25821) := by
  kernel_rfl
theorem node1260_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2341 state64 453 state65 = (program38677,state13392,25821) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2341
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1258_eq, node1259_eq]
  kernel_rfl
theorem node1261_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state13392 25821 state65 = (program38678,state13402,25825) := by
  kernel_rfl
theorem node1262_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2342 state64 453 state65 = (program38679,state13402,25825) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2342
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1260_eq, node1261_eq]
  kernel_rfl
theorem node1263_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state13402 25825 state65 = (program38740,state13444,25949) := by
  kernel_rfl
theorem node1264_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2343 state64 453 state65 = (program38741,state13444,25949) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2343
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1262_eq, node1263_eq]
  kernel_rfl
theorem node1265_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2347 state13444 25949 state65 = (program38750,state13463,25969) := by
  kernel_rfl
theorem node1266_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2348 state64 453 state65 = (program38751,state13463,25969) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2348
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1264_eq, node1265_eq]
  kernel_rfl
theorem node1267_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2349 state13463 25969 state65 = (program38752,state13471,25973) := by
  kernel_rfl
theorem node1268_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2350 state64 453 state65 = (program38753,state13471,25973) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2350
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1266_eq, node1267_eq]
  kernel_rfl
theorem node1269_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2354 state13471 25973 state65 = (program38762,state13495,25993) := by
  kernel_rfl
theorem node1270_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2355 state64 453 state65 = (program38763,state13495,25993) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2355
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1268_eq, node1269_eq]
  kernel_rfl
theorem node1271_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2356 state13495 25993 state65 = (program38764,state13507,25997) := by
  kernel_rfl
theorem node1272_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2357 state64 453 state65 = (program38765,state13507,25997) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2357
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1270_eq, node1271_eq]
  kernel_rfl
theorem node1273_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2361 state13507 25997 state65 = (program38773,state13530,26017) := by
  kernel_rfl
theorem node1274_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2362 state64 453 state65 = (program38774,state13530,26017) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2362
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1272_eq, node1273_eq]
  kernel_rfl
theorem node1275_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2363 state13530 26017 state65 = (InitECandidate.Proofs.WordStages.word154_2_12902,state13541,26021) := by
  kernel_rfl
theorem node1276_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2364 state64 453 state65 = (program38775,state13541,26021) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2364
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1274_eq, node1275_eq]
  kernel_rfl
theorem node1277_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2368 state13541 26021 state65 = (program38784,state13565,26041) := by
  kernel_rfl
theorem node1278_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2369 state64 453 state65 = (program38785,state13565,26041) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2369
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node1276_eq, node1277_eq]
  kernel_rfl
theorem node1279_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2370 state13565 26041 state65 = (program38786,state13578,26045) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
