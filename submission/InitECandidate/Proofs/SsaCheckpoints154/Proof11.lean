import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof10
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node704_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2063 state64 453 state65 = (program32233,state7104,12929) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2063
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node702_eq, node703_eq]
  kernel_rfl
theorem node705_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state7104 12929 state65 = (program32294,state7146,13053) := by
  kernel_rfl
theorem node706_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2064 state64 453 state65 = (program32295,state7146,13053) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2064
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node704_eq, node705_eq]
  kernel_rfl
theorem node707_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1399 state7146 13053 state65 = (program32356,state7182,13177) := by
  kernel_rfl
theorem node708_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1400 state7182 13177 state65 = (program32359,state7200,13185) := by
  kernel_rfl
theorem node709_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1401 state7146 13053 state65 = (program32360,state7200,13185) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1401
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node707_eq, node708_eq]
  kernel_rfl
theorem node710_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state7200 13185 state65 = (program32361,state7208,13189) := by
  kernel_rfl
theorem node711_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1402 state7146 13053 state65 = (program32362,state7208,13189) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1402
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node709_eq, node710_eq]
  kernel_rfl
theorem node712_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state7208 13189 state65 = (program32363,state7216,13193) := by
  kernel_rfl
theorem node713_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1403 state7146 13053 state65 = (program32364,state7216,13193) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1403
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node711_eq, node712_eq]
  kernel_rfl
theorem node714_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2065 state64 453 state65 = (program32365,state7216,13193) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2065
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node706_eq, node713_eq]
  kernel_rfl
theorem node715_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1405 state7216 13193 state65 = (program32366,state7227,13197) := by
  kernel_rfl
theorem node716_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2066 state64 453 state65 = (program32367,state7227,13197) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2066
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node714_eq, node715_eq]
  kernel_rfl
theorem node717_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2069 state7227 13197 state65 = (program32428,state7270,13321) := by
  kernel_rfl
theorem node718_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2070 state64 453 state65 = (program32429,state7270,13321) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2070
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node716_eq, node717_eq]
  kernel_rfl
theorem node719_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state7270 13321 state65 = (program32438,state7296,13341) := by
  kernel_rfl
theorem node720_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2071 state64 453 state65 = (program32439,state7296,13341) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2071
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node718_eq, node719_eq]
  kernel_rfl
theorem node721_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state7296 13341 state65 = (program32440,state7309,13345) := by
  kernel_rfl
theorem node722_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2072 state64 453 state65 = (program32441,state7309,13345) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2072
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node720_eq, node721_eq]
  kernel_rfl
theorem node723_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state7309 13345 state65 = (program32502,state7352,13469) := by
  kernel_rfl
theorem node724_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2073 state64 453 state65 = (program32503,state7352,13469) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2073
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node722_eq, node723_eq]
  kernel_rfl
theorem node725_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1451 state7352 13469 state65 = (program32564,state7389,13593) := by
  kernel_rfl
theorem node726_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1452 state7389 13593 state65 = (program32567,state7407,13601) := by
  kernel_rfl
theorem node727_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1453 state7352 13469 state65 = (program32568,state7407,13601) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1453
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node725_eq, node726_eq]
  kernel_rfl
theorem node728_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state7407 13601 state65 = (program32569,state7415,13605) := by
  kernel_rfl
theorem node729_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1454 state7352 13469 state65 = (program32570,state7415,13605) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1454
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node727_eq, node728_eq]
  kernel_rfl
theorem node730_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state7415 13605 state65 = (program32571,state7423,13609) := by
  kernel_rfl
theorem node731_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1455 state7352 13469 state65 = (program32572,state7423,13609) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1455
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node729_eq, node730_eq]
  kernel_rfl
theorem node732_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2074 state64 453 state65 = (program32573,state7423,13609) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2074
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node724_eq, node731_eq]
  kernel_rfl
theorem node733_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1457 state7423 13609 state65 = (program32574,state7434,13613) := by
  kernel_rfl
theorem node734_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2075 state64 453 state65 = (program32575,state7434,13613) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2075
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node732_eq, node733_eq]
  kernel_rfl
theorem node735_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2078 state7434 13613 state65 = (program32636,state7476,13737) := by
  kernel_rfl
theorem node736_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2079 state64 453 state65 = (program32637,state7476,13737) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2079
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node734_eq, node735_eq]
  kernel_rfl
theorem node737_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state7476 13737 state65 = (program32646,state7499,13757) := by
  kernel_rfl
theorem node738_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2080 state64 453 state65 = (program32647,state7499,13757) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2080
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node736_eq, node737_eq]
  kernel_rfl
theorem node739_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state7499 13757 state65 = (program32648,state7511,13761) := by
  kernel_rfl
theorem node740_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2081 state64 453 state65 = (program32649,state7511,13761) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2081
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node738_eq, node739_eq]
  kernel_rfl
theorem node741_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state7511 13761 state65 = (program32710,state7553,13885) := by
  kernel_rfl
theorem node742_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2082 state64 453 state65 = (program32711,state7553,13885) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2082
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node740_eq, node741_eq]
  kernel_rfl
theorem node743_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1502 state7553 13885 state65 = (program32772,state7585,14009) := by
  kernel_rfl
theorem node744_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1503 state7585 14009 state65 = (program32775,state7602,14017) := by
  kernel_rfl
theorem node745_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1504 state7553 13885 state65 = (program32776,state7602,14017) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1504
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node743_eq, node744_eq]
  kernel_rfl
theorem node746_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state7602 14017 state65 = (program32777,state7610,14021) := by
  kernel_rfl
theorem node747_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1505 state7553 13885 state65 = (program32778,state7610,14021) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1505
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node745_eq, node746_eq]
  kernel_rfl
theorem node748_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state7610 14021 state65 = (program32779,state7618,14025) := by
  kernel_rfl
theorem node749_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1506 state7553 13885 state65 = (program32780,state7618,14025) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1506
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node747_eq, node748_eq]
  kernel_rfl
theorem node750_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2083 state64 453 state65 = (program32781,state7618,14025) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2083
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node742_eq, node749_eq]
  kernel_rfl
theorem node751_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1508 state7618 14025 state65 = (program32782,state7627,14029) := by
  kernel_rfl
theorem node752_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2084 state64 453 state65 = (program32783,state7627,14029) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2084
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node750_eq, node751_eq]
  kernel_rfl
theorem node753_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2087 state7627 14029 state65 = (program32844,state7671,14153) := by
  kernel_rfl
theorem node754_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2088 state64 453 state65 = (program32845,state7671,14153) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2088
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node752_eq, node753_eq]
  kernel_rfl
theorem node755_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state7671 14153 state65 = (program32854,state7694,14173) := by
  kernel_rfl
theorem node756_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2089 state64 453 state65 = (program32855,state7694,14173) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2089
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node754_eq, node755_eq]
  kernel_rfl
theorem node757_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state7694 14173 state65 = (program32856,state7704,14177) := by
  kernel_rfl
theorem node758_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2090 state64 453 state65 = (program32857,state7704,14177) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2090
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node756_eq, node757_eq]
  kernel_rfl
theorem node759_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state7704 14177 state65 = (program32918,state7746,14301) := by
  kernel_rfl
theorem node760_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_2091 state64 453 state65 = (program32919,state7746,14301) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_2091
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node758_eq, node759_eq]
  kernel_rfl
theorem node761_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1551 state7746 14301 state65 = (program32980,state7781,14425) := by
  kernel_rfl
theorem node762_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1552 state7781 14425 state65 = (program32983,state7800,14433) := by
  kernel_rfl
theorem node763_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1553 state7746 14301 state65 = (program32984,state7800,14433) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1553
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node761_eq, node762_eq]
  kernel_rfl
theorem node764_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_590 state7800 14433 state65 = (program32985,state7808,14437) := by
  kernel_rfl
theorem node765_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1554 state7746 14301 state65 = (program32986,state7808,14437) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1554
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node763_eq, node764_eq]
  kernel_rfl
theorem node766_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_592 state7808 14437 state65 = (program32987,state7816,14441) := by
  kernel_rfl
theorem node767_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1555 state7746 14301 state65 = (program32988,state7816,14441) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1555
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node765_eq, node766_eq]
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
