import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SsaCheckpoints154.Proof0
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Proofs.SmallSsaKernelComputation
namespace InitECandidate.Proofs.SsaCheckpoints154
theorem node64_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_185 state64 453 state65 = (program26274,state526,909) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_185
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node62_eq, node63_eq]
  kernel_rfl
theorem node65_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_95 state526 909 state65 = (program26275,state533,913) := by
  kernel_rfl
theorem node66_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_187 state64 453 state65 = (program26276,state533,913) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_187
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node64_eq, node65_eq]
  kernel_rfl
theorem node67_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_189 state533 913 state65 = (program26279,state548,921) := by
  kernel_rfl
theorem node68_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_190 state64 453 state65 = (program26280,state548,921) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_190
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node66_eq, node67_eq]
  kernel_rfl
theorem node69_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_99 state548 921 state65 = (program26281,state556,925) := by
  kernel_rfl
theorem node70_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_192 state64 453 state65 = (program26282,state556,925) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_192
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node68_eq, node69_eq]
  kernel_rfl
theorem node71_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_194 state556 925 state65 = (program26285,state567,933) := by
  kernel_rfl
theorem node72_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_195 state64 453 state65 = (program26286,state567,933) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_195
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node70_eq, node71_eq]
  kernel_rfl
theorem node73_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_103 state567 933 state65 = (program26287,state571,937) := by
  kernel_rfl
theorem node74_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_197 state64 453 state65 = (program26288,state571,937) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_197
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node72_eq, node73_eq]
  kernel_rfl
theorem node75_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_211 state571 937 state65 = (program26307,state601,977) := by
  kernel_rfl
theorem node76_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_212 state64 453 state65 = (program26308,state601,977) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_212
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node74_eq, node75_eq]
  kernel_rfl
theorem node77_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_214 state601 977 state65 = (program26311,state614,985) := by
  kernel_rfl
theorem node78_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_215 state64 453 state65 = (program26312,state614,985) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_215
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node76_eq, node77_eq]
  kernel_rfl
theorem node79_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_109 state614 985 state65 = (program26313,state620,989) := by
  kernel_rfl
theorem node80_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_217 state64 453 state65 = (program26314,state620,989) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_217
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node78_eq, node79_eq]
  kernel_rfl
theorem node81_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_219 state620 989 state65 = (program26317,state635,997) := by
  kernel_rfl
theorem node82_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_220 state64 453 state65 = (program26318,state635,997) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_220
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node80_eq, node81_eq]
  kernel_rfl
theorem node83_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_113 state635 997 state65 = (program26319,state643,1001) := by
  kernel_rfl
theorem node84_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_222 state64 453 state65 = (program26320,state643,1001) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_222
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node82_eq, node83_eq]
  kernel_rfl
theorem node85_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_224 state643 1001 state65 = (program26323,state656,1009) := by
  kernel_rfl
theorem node86_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_225 state64 453 state65 = (program26324,state656,1009) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_225
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node84_eq, node85_eq]
  kernel_rfl
theorem node87_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_117 state656 1009 state65 = (program26325,state662,1013) := by
  kernel_rfl
theorem node88_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_227 state64 453 state65 = (program26326,state662,1013) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_227
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node86_eq, node87_eq]
  kernel_rfl
theorem node89_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_229 state662 1013 state65 = (program26329,state676,1021) := by
  kernel_rfl
theorem node90_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_230 state64 453 state65 = (program26330,state676,1021) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_230
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node88_eq, node89_eq]
  kernel_rfl
theorem node91_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_121 state676 1021 state65 = (program26331,state683,1025) := by
  kernel_rfl
theorem node92_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_232 state64 453 state65 = (program26332,state683,1025) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_232
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node90_eq, node91_eq]
  kernel_rfl
theorem node93_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_246 state683 1025 state65 = (program26351,state713,1065) := by
  kernel_rfl
theorem node94_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_247 state64 453 state65 = (program26352,state713,1065) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_247
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node92_eq, node93_eq]
  kernel_rfl
theorem node95_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_249 state713 1065 state65 = (program26355,state728,1073) := by
  kernel_rfl
theorem node96_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_250 state64 453 state65 = (program26356,state728,1073) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_250
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node94_eq, node95_eq]
  kernel_rfl
theorem node97_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_127 state728 1073 state65 = (program26357,state736,1077) := by
  kernel_rfl
theorem node98_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_252 state64 453 state65 = (program26358,state736,1077) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_252
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node96_eq, node97_eq]
  kernel_rfl
theorem node99_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_254 state736 1077 state65 = (program26361,state748,1085) := by
  kernel_rfl
theorem node100_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_255 state64 453 state65 = (program26362,state748,1085) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_255
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node98_eq, node99_eq]
  kernel_rfl
theorem node101_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_131 state748 1085 state65 = (program26363,state753,1089) := by
  kernel_rfl
theorem node102_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_257 state64 453 state65 = (program26364,state753,1089) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_257
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node100_eq, node101_eq]
  kernel_rfl
theorem node103_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_259 state753 1089 state65 = (program26367,state767,1097) := by
  kernel_rfl
theorem node104_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_260 state64 453 state65 = (program26368,state767,1097) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_260
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node102_eq, node103_eq]
  kernel_rfl
theorem node105_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_135 state767 1097 state65 = (program26369,state774,1101) := by
  kernel_rfl
theorem node106_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_262 state64 453 state65 = (program26370,state774,1101) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_262
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node104_eq, node105_eq]
  kernel_rfl
theorem node107_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_264 state774 1101 state65 = (program26373,state788,1109) := by
  kernel_rfl
theorem node108_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_265 state64 453 state65 = (program26374,state788,1109) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_265
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node106_eq, node107_eq]
  kernel_rfl
theorem node109_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_139 state788 1109 state65 = (program26375,state795,1113) := by
  kernel_rfl
theorem node110_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_267 state64 453 state65 = (program26376,state795,1113) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_267
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node108_eq, node109_eq]
  kernel_rfl
theorem node111_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_281 state795 1113 state65 = (program26395,state829,1153) := by
  kernel_rfl
theorem node112_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_282 state64 453 state65 = (program26396,state829,1153) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_282
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node110_eq, node111_eq]
  kernel_rfl
theorem node113_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_283 state829 1153 state65 = (program26397,state836,1157) := by
  kernel_rfl
theorem node114_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_284 state64 453 state65 = (program26398,state836,1157) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_284
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node112_eq, node113_eq]
  kernel_rfl
theorem node115_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_145 state836 1157 state65 = (program26399,state842,1161) := by
  kernel_rfl
theorem node116_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_286 state64 453 state65 = (program26400,state842,1161) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_286
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node114_eq, node115_eq]
  kernel_rfl
theorem node117_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_289 state842 1161 state65 = (program26403,state858,1169) := by
  kernel_rfl
theorem node118_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_290 state64 453 state65 = (program26404,state858,1169) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_290
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node116_eq, node117_eq]
  kernel_rfl
theorem node119_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_149 state858 1169 state65 = (program26405,state866,1173) := by
  kernel_rfl
theorem node120_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_292 state64 453 state65 = (program26406,state866,1173) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_292
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node118_eq, node119_eq]
  kernel_rfl
theorem node121_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_294 state866 1173 state65 = (program26409,state880,1181) := by
  kernel_rfl
theorem node122_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_295 state64 453 state65 = (program26410,state880,1181) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_295
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node120_eq, node121_eq]
  kernel_rfl
theorem node123_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_153 state880 1181 state65 = (InitECandidate.Proofs.WordStages.word154_2_484,state887,1185) := by
  kernel_rfl
theorem node124_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_297 state64 453 state65 = (program26411,state887,1185) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_297
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node122_eq, node123_eq]
  kernel_rfl
theorem node125_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_299 state887 1185 state65 = (program26413,state902,1193) := by
  kernel_rfl
theorem node126_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_1_300 state64 453 state65 = (program26414,state902,1193) := by
  unfold InitECandidate.Proofs.WordStages.word154_1_300
  rw [ssaStructural.eq_def]
  dsimp only
  rw [node124_eq, node125_eq]
  kernel_rfl
theorem node127_eq : ssaStructural InitECandidate.Proofs.WordStages.word154_0_157 state902 1193 state65 = (InitECandidate.Proofs.WordStages.word154_2_490,state910,1197) := by
  kernel_rfl
end InitECandidate.Proofs.SsaCheckpoints154
