import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof4
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node320_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_992 state64 453 state65 = (program27408,state2473,3261) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_992
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node318_eq, node319_eq]
  kernel_rfl
theorem node321_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1023 state2473 3261 state65 = (program27469,state2518,3385) := by
  kernel_rfl
theorem node322_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1024 state64 453 state65 = (program27470,state2518,3385) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1024
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node320_eq, node321_eq]
  kernel_rfl
theorem node323_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1028 state2518 3385 state65 = (program27479,state2542,3405) := by
  kernel_rfl
theorem node324_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1029 state64 453 state65 = (program27480,state2542,3405) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1029
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node322_eq, node323_eq]
  kernel_rfl
theorem node325_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1030 state2542 3405 state65 = (program27481,state2553,3409) := by
  kernel_rfl
theorem node326_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1031 state64 453 state65 = (program27482,state2553,3409) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1031
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node324_eq, node325_eq]
  kernel_rfl
theorem node327_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1059 state2553 3409 state65 = (program27542,state2594,3533) := by
  kernel_rfl
theorem node328_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1060 state64 453 state65 = (program27543,state2594,3533) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1060
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node326_eq, node327_eq]
  kernel_rfl
theorem node329_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1089 state2594 3533 state65 = (program27604,state2638,3657) := by
  kernel_rfl
theorem node330_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1090 state64 453 state65 = (program27605,state2638,3657) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1090
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node328_eq, node329_eq]
  kernel_rfl
theorem node331_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1094 state2638 3657 state65 = (program27614,state2660,3677) := by
  kernel_rfl
theorem node332_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1095 state64 453 state65 = (program27615,state2660,3677) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1095
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node330_eq, node331_eq]
  kernel_rfl
theorem node333_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1096 state2660 3677 state65 = (program27616,state2670,3681) := by
  kernel_rfl
theorem node334_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1097 state64 453 state65 = (program27617,state2670,3681) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1097
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node332_eq, node333_eq]
  kernel_rfl
theorem node335_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1125 state2670 3681 state65 = (program27677,state2712,3805) := by
  kernel_rfl
theorem node336_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1126 state64 453 state65 = (program27678,state2712,3805) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1126
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node334_eq, node335_eq]
  kernel_rfl
theorem node337_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1154 state2712 3805 state65 = (program27739,state2754,3929) := by
  kernel_rfl
theorem node338_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1155 state64 453 state65 = (program27740,state2754,3929) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1155
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node336_eq, node337_eq]
  kernel_rfl
theorem node339_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1158 state2754 3929 state65 = (program27749,state2780,3949) := by
  kernel_rfl
theorem node340_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1159 state64 453 state65 = (program27750,state2780,3949) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1159
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node338_eq, node339_eq]
  kernel_rfl
theorem node341_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_595 state2780 3949 state65 = (program27751,state2793,3953) := by
  kernel_rfl
theorem node342_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1160 state64 453 state65 = (program27752,state2793,3953) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1160
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node340_eq, node341_eq]
  kernel_rfl
theorem node343_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1187 state2793 3953 state65 = (program27812,state2835,4077) := by
  kernel_rfl
theorem node344_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1188 state64 453 state65 = (program27813,state2835,4077) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1188
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node342_eq, node343_eq]
  kernel_rfl
theorem node345_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1199 state2835 4077 state65 = (program27874,state2880,4201) := by
  kernel_rfl
theorem node346_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1200 state64 453 state65 = (program27875,state2880,4201) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1200
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node344_eq, node345_eq]
  kernel_rfl
theorem node347_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1203 state2880 4201 state65 = (program27884,state2906,4221) := by
  kernel_rfl
theorem node348_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1204 state64 453 state65 = (program27885,state2906,4221) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1204
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node346_eq, node347_eq]
  kernel_rfl
theorem node349_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_654 state2906 4221 state65 = (program27886,state2919,4225) := by
  kernel_rfl
theorem node350_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1205 state64 453 state65 = (program27887,state2919,4225) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1205
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node348_eq, node349_eq]
  kernel_rfl
theorem node351_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1215 state2919 4225 state65 = (program27947,state2962,4349) := by
  kernel_rfl
theorem node352_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1216 state64 453 state65 = (program27948,state2962,4349) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1216
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node350_eq, node351_eq]
  kernel_rfl
theorem node353_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1226 state2962 4349 state65 = (program28009,state3005,4473) := by
  kernel_rfl
theorem node354_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1227 state64 453 state65 = (program28010,state3005,4473) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1227
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node352_eq, node353_eq]
  kernel_rfl
theorem node355_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1230 state3005 4473 state65 = (program28019,state3028,4493) := by
  kernel_rfl
theorem node356_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1231 state64 453 state65 = (program28020,state3028,4493) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1231
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node354_eq, node355_eq]
  kernel_rfl
theorem node357_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_740 state3028 4493 state65 = (program28021,state3040,4497) := by
  kernel_rfl
theorem node358_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1232 state64 453 state65 = (program28022,state3040,4497) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1232
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node356_eq, node357_eq]
  kernel_rfl
theorem node359_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1240 state3040 4497 state65 = (program28082,state3082,4621) := by
  kernel_rfl
theorem node360_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1241 state64 453 state65 = (program28083,state3082,4621) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1241
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node358_eq, node359_eq]
  kernel_rfl
theorem node361_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1248 state3082 4621 state65 = (program28144,state3127,4745) := by
  kernel_rfl
theorem node362_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1249 state64 453 state65 = (program28145,state3127,4745) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1249
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node360_eq, node361_eq]
  kernel_rfl
theorem node363_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1252 state3127 4745 state65 = (program28154,state3150,4765) := by
  kernel_rfl
theorem node364_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1253 state64 453 state65 = (program28155,state3150,4765) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1253
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node362_eq, node363_eq]
  kernel_rfl
theorem node365_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_813 state3150 4765 state65 = (program28156,state3160,4769) := by
  kernel_rfl
theorem node366_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1254 state64 453 state65 = (program28157,state3160,4769) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1254
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node364_eq, node365_eq]
  kernel_rfl
theorem node367_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_846 state3160 4769 state65 = (program28217,state3202,4893) := by
  kernel_rfl
theorem node368_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1255 state64 453 state65 = (program28218,state3202,4893) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1255
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node366_eq, node367_eq]
  kernel_rfl
theorem node369_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1262 state3202 4893 state65 = (program28279,state3244,5017) := by
  kernel_rfl
theorem node370_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1263 state64 453 state65 = (program28280,state3244,5017) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1263
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node368_eq, node369_eq]
  kernel_rfl
theorem node371_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_886 state3244 5017 state65 = (program28289,state3270,5037) := by
  kernel_rfl
theorem node372_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1264 state64 453 state65 = (program28290,state3270,5037) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1264
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node370_eq, node371_eq]
  kernel_rfl
theorem node373_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_888 state3270 5037 state65 = (program28291,state3283,5041) := by
  kernel_rfl
theorem node374_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1265 state64 453 state65 = (program28292,state3283,5041) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1265
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node372_eq, node373_eq]
  kernel_rfl
theorem node375_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_922 state3283 5041 state65 = (program28352,state3323,5165) := by
  kernel_rfl
theorem node376_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1266 state64 453 state65 = (program28353,state3323,5165) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1266
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node374_eq, node375_eq]
  kernel_rfl
theorem node377_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1273 state3323 5165 state65 = (program28414,state3367,5289) := by
  kernel_rfl
theorem node378_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1274 state64 453 state65 = (program28415,state3367,5289) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1274
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node376_eq, node377_eq]
  kernel_rfl
theorem node379_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_959 state3367 5289 state65 = (program28424,state3393,5309) := by
  kernel_rfl
theorem node380_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1275 state64 453 state65 = (program28425,state3393,5309) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1275
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node378_eq, node379_eq]
  kernel_rfl
theorem node381_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_961 state3393 5309 state65 = (program28426,state3406,5313) := by
  kernel_rfl
theorem node382_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_1276 state64 453 state65 = (program28427,state3406,5313) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_1276
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node380_eq, node381_eq]
  kernel_rfl
theorem node383_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_991 state3406 5313 state65 = (program28487,state3447,5437) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
