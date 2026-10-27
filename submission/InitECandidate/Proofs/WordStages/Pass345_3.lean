import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass345_2
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word345_3_6 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_9

def word345_3_10 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_6 word345_2_13

def word345_3_12 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_10 word345_2_15

def word345_3_16 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_12 word345_2_19

def word345_3_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 77 (Flapjack.WordRegImm.reg 81) word345_3_16 word345_0_16

def word345_3_19 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_18 word345_0_4

def word345_3_20 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_3 word345_3_19

def word345_3_21 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_20 word345_0_4

def word345_3_23 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_21 word345_2_48

def word345_3_25 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_23 word345_2_50

def word345_3_27 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_25 word345_2_52

def word345_3_29 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_27 word345_2_56

def word345_3_34 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_60 word345_2_61

def word345_3_36 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_34 word345_2_65

def word345_3_43 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_75 word345_2_76

def word345_3_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_3_36, 345, 2)) (some 68) ([2]) (some (2, word345_3_43, 345, 3))

def word345_3_45 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_59 word345_3_44

def word345_3_46 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_58 word345_3_45

def word345_3_47 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_29 word345_3_46

def word345_3_48 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_47 word345_0_4

def word345_3_50 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_48 word345_2_87

def word345_3_52 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_50 word345_2_91

def word345_3_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
            (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_2_95, 345, 4)) (some 78) ([2, 4]) (some (2, word345_2_109, 345, 5))

def word345_3_62 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_94 word345_3_61

def word345_3_63 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_93 word345_3_62

def word345_3_64 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_52 word345_3_63

def word345_3_65 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_64 word345_0_4

def word345_3_69 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_65 word345_2_123

def word345_3_71 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_69 word345_2_125

def word345_3_73 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_71 word345_2_127

def word345_3_77 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_73 word345_2_131

def word345_3_81 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_77 word345_2_135

def word345_3_83 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_81 word345_2_137

def word345_3_85 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_83 word345_2_139

def word345_3_89 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_85 word345_2_143

def word345_3_91 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_89 word345_2_145

def word345_3_93 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_91 word345_2_147

def word345_3_95 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_93 word345_2_149

def word345_3_97 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_95 word345_2_151

def word345_3_99 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_159

def word345_3_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(361, 341)]

def word345_3_101 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_99 word345_3_100

def word345_3_103 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_170

def word345_3_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(361, 357)]

def word345_3_105 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_103 word345_3_104

def word345_3_106 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 321 (Flapjack.WordRegImm.reg 325) word345_3_101 word345_3_105

def word345_3_107 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_97 word345_3_106

def word345_3_108 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_107 word345_0_4

def word345_3_110 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_108 word345_2_178

def word345_3_112 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_110 word345_2_180

def word345_3_114 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_188

def word345_3_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(413, 393)]

def word345_3_116 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_114 word345_3_115

def word345_3_118 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_199

def word345_3_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(413, 409)]

def word345_3_120 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_118 word345_3_119

def word345_3_121 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 373 (Flapjack.WordRegImm.reg 377) word345_3_116 word345_3_120

def word345_3_122 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_112 word345_3_121

def word345_3_123 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_122 word345_0_4

def word345_3_129 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_123 word345_2_211

def word345_3_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(489, 2), (493, 4), (497, 6)]

def word345_3_141 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_222 word345_3_140

def word345_3_144 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_226 word345_2_228

def word345_3_146 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_144 word345_2_232

def word345_3_147 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_141 word345_3_146

def word345_3_155 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_243 word345_2_245

def word345_3_157 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_155 word345_2_249

def word345_3_158 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_242 word345_3_157

def word345_3_159 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_147, 345, 6)) (some 162) ([2, 4]) (some (2, word345_3_158, 345, 7))

def word345_3_160 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_221 word345_3_159

def word345_3_161 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_220 word345_3_160

def word345_3_162 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_219 word345_3_161

def word345_3_163 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_162 word345_0_4

def word345_3_165 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_163 word345_2_260

def word345_3_167 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_165 word345_2_262

def word345_3_169 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_167 word345_2_264

def word345_3_171 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_270

def word345_3_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(569, 549)]

def word345_3_173 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_171 word345_3_172

def word345_3_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(569, 481)]

def word345_3_175 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_3_174

def word345_3_176 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 533 (Flapjack.WordRegImm.reg 537) word345_3_173 word345_3_175

def word345_3_177 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_169 word345_3_176

def word345_3_178 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_177 word345_0_4

def word345_3_180 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_178 word345_2_285

def word345_3_182 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_180 word345_2_287

def word345_3_184 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_293

def word345_3_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(609, 589)]

def word345_3_186 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_184 word345_3_185

def word345_3_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(609, 569)]

def word345_3_188 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_3_187

def word345_3_189 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 573 (Flapjack.WordRegImm.reg 577) word345_3_186 word345_3_188

def word345_3_190 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_182 word345_3_189

def word345_3_191 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_190 word345_0_4

def word345_3_193 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_191 word345_2_308

def word345_3_195 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_193 word345_2_310

def word345_3_197 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_316

def word345_3_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(649, 629)]

def word345_3_199 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_197 word345_3_198

def word345_3_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(649, 609)]

def word345_3_201 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_3_200

def word345_3_202 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 613 (Flapjack.WordRegImm.reg 617) word345_3_199 word345_3_201

def word345_3_203 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_195 word345_3_202

def word345_3_204 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_203 word345_0_4

def word345_3_206 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_204 word345_2_331

def word345_3_208 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_206 word345_2_333

def word345_3_210 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_339

def word345_3_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(689, 669)]

def word345_3_212 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_210 word345_3_211

def word345_3_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(689, 649)]

def word345_3_214 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_3_213

def word345_3_215 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 653 (Flapjack.WordRegImm.reg 657) word345_3_212 word345_3_214

def word345_3_216 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_208 word345_3_215

def word345_3_217 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_216 word345_0_4

def word345_3_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(945, 473), (937, 521), (929, 689), (925, 513), (921, 485), (917, 653), (913, 509)]

def word345_3_219 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_217 word345_3_218

def word345_3_224 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_374

def word345_3_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(733, 713)]

def word345_3_226 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_224 word345_3_225

def word345_3_228 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_385

def word345_3_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(733, 729)]

def word345_3_230 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_228 word345_3_229

def word345_3_231 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 693 (Flapjack.WordRegImm.reg 697) word345_3_226 word345_3_230

def word345_3_232 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_367 word345_3_231

def word345_3_233 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_232 word345_0_4

def word345_3_235 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_233 word345_2_393

def word345_3_237 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_235 word345_2_395

def word345_3_239 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_403

def word345_3_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(785, 765)]

def word345_3_241 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_239 word345_3_240

def word345_3_243 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_414

def word345_3_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(785, 781)]

def word345_3_245 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_243 word345_3_244

def word345_3_246 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 745 (Flapjack.WordRegImm.reg 749) word345_3_241 word345_3_245

def word345_3_247 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_237 word345_3_246

def word345_3_248 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_247 word345_0_4

def word345_3_254 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_248 word345_2_426

def word345_3_265 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 805 (Flapjack.WordRegImm.imm 0#64) word345_0_16 word345_2_442

def word345_3_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(873, 2), (877, 4), (881, 6)]

def word345_3_273 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_454 word345_3_272

def word345_3_276 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_458 word345_2_460

def word345_3_278 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_276 word345_2_464

def word345_3_279 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_273 word345_3_278

def word345_3_287 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_475 word345_2_477

def word345_3_289 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_287 word345_2_481

def word345_3_290 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_474 word345_3_289

def word345_3_291 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_279, 345, 8)) (some 162) ([2, 4]) (some (2, word345_3_290, 345, 9))

def word345_3_292 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_453 word345_3_291

def word345_3_293 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_452 word345_3_292

def word345_3_294 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_451 word345_3_293

def word345_3_295 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_294 word345_0_4

def word345_3_296 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_265 word345_3_295

def word345_3_297 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_254 word345_3_296

def word345_3_298 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_297 word345_0_4

def word345_3_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(945, 857), (937, 905), (929, 861), (925, 897), (921, 865), (917, 869), (913, 893)]

def word345_3_300 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_298 word345_3_299

def word345_3_301 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 433 (Flapjack.WordRegImm.imm 0#64) word345_3_219 word345_3_300

def word345_3_302 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_129 word345_3_301

def word345_3_303 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_302 word345_0_4

def word345_3_305 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_303 word345_2_509

def word345_3_307 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_305 word345_2_511

def word345_3_309 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_307 word345_2_513

def word345_3_313 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_309 word345_2_517

def word345_3_315 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_313 word345_2_519

def word345_3_317 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_315 word345_2_521

def word345_3_319 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_527

def word345_3_323 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_319 word345_2_531

def word345_3_325 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_323 word345_2_533

def word345_3_328 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_325 word345_2_536

def word345_3_329 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 981 (Flapjack.WordRegImm.reg 985) word345_3_328 word345_0_16

def word345_3_330 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_329 word345_0_4

def word345_3_331 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_317 word345_3_330

def word345_3_332 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_331 word345_0_4

def word345_3_334 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_332 word345_2_552

def word345_3_336 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_334 word345_2_554

def word345_3_341 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_558 word345_2_559

def word345_3_344 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_564 word345_2_566

def word345_3_345 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_341 word345_3_344

def word345_3_353 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_577 word345_2_579

def word345_3_354 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_574 word345_3_353

def word345_3_355 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_3_345, 345, 10)) (some 169) ([2, 4]) (some (2, word345_3_354, 345, 11))

def word345_3_356 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_557 word345_3_355

def word345_3_357 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_556 word345_3_356

def word345_3_358 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_336 word345_3_357

def word345_3_359 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_358 word345_0_4

def word345_3_361 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_359 word345_2_588

def word345_3_363 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_361 word345_2_590

def word345_3_365 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_363 word345_2_592

def word345_3_367 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_598

def word345_3_371 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_367 word345_2_602

def word345_3_373 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_371 word345_2_604

def word345_3_376 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_373 word345_2_607

def word345_3_377 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 1105 (Flapjack.WordRegImm.reg 1109) word345_3_376 word345_0_16

def word345_3_378 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_377 word345_0_4

def word345_3_379 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_365 word345_3_378

def word345_3_380 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_379 word345_0_4

def word345_3_382 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_380 word345_2_635

def word345_3_384 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_382 word345_2_637

def word345_3_386 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_384 word345_2_639

def word345_3_388 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_645

def word345_3_390 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_388 word345_2_659

def word345_3_392 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_390 word345_2_661

def word345_3_394 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_392 word345_2_663

def word345_3_399 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_667 word345_2_668

def word345_3_401 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_399 word345_2_671

def word345_3_408 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_681 word345_2_682

def word345_3_409 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_401, 345, 12)) (some 337) ([2, 4, 6, 8]) (some (2, word345_3_408, 345, 13))

def word345_3_410 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_666 word345_3_409

def word345_3_411 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_665 word345_3_410

def word345_3_412 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_394 word345_3_411

def word345_3_413 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_412 word345_0_4

def word345_3_417 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_413 word345_2_695

def word345_3_419 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_417 word345_2_697

def word345_3_421 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_419 word345_2_699

def word345_3_425 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_421 word345_2_703

def word345_3_427 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_425 word345_2_705

def word345_3_428 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1333, 1237), (1317, 1289), (1309, 1269), (1305, 1245), (1301, 1249)]

def word345_3_429 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_427 word345_3_428

def word345_3_430 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1333, 1061), (1317, 1157), (1309, 1069), (1305, 1161), (1301, 1101)]

def word345_3_431 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_3_430

def word345_3_432 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 1161 (Flapjack.WordRegImm.reg 1165) word345_3_429 word345_3_431

def word345_3_433 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_386 word345_3_432

def word345_3_434 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_433 word345_0_4

def word345_3_436 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_434 word345_2_736

def word345_3_438 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_436 word345_2_738

def word345_3_440 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_744

def word345_3_442 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_440 word345_2_746

def word345_3_444 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_442 word345_2_756

def word345_3_446 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_444 word345_2_758

def word345_3_451 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_762 word345_2_763

def word345_3_453 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_451 word345_2_766

def word345_3_460 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_776 word345_2_777

def word345_3_461 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word345_3_453, 345, 14)) (some 337) ([2, 4, 6, 8]) (some (2, word345_3_460, 345, 15))

def word345_3_462 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_761 word345_3_461

def word345_3_463 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_760 word345_3_462

def word345_3_464 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_446 word345_3_463

def word345_3_465 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_464 word345_0_4

def word345_3_467 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_465 word345_2_788

def word345_3_469 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_467 word345_2_790

def word345_3_471 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_469 word345_2_792

def word345_3_473 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_471 word345_2_794

def word345_3_474 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(1629, 1429), (1625, 1465), (1621, 1473), (1613, 1469), (1609, 1433), (1605, 1437), (1601, 1441), (1597, 1477),
    (1593, 1445)]

def word345_3_475 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_473 word345_3_474

def word345_3_477 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_805

def word345_3_479 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_477 word345_2_807

def word345_3_481 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_479 word345_2_813

def word345_3_486 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_817 word345_2_818

def word345_3_489 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_821 word345_2_823

def word345_3_491 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_489 word345_2_827

def word345_3_493 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_491 word345_2_829

def word345_3_494 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_486 word345_3_493

def word345_3_502 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_838 word345_2_840

def word345_3_504 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_502 word345_2_844

def word345_3_506 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_504 word345_2_846

def word345_3_507 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_837 word345_3_506

def word345_3_508 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_494, 345, 16)) (some 336) ([2, 4, 6]) (some (2, word345_3_507, 345, 17))

def word345_3_509 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_816 word345_3_508

def word345_3_510 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_815 word345_3_509

def word345_3_511 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_481 word345_3_510

def word345_3_512 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_511 word345_0_4

def word345_3_513 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(1629, 1533), (1625, 1589), (1621, 1585), (1613, 1577), (1609, 1537), (1605, 1541), (1601, 1545), (1597, 1573),
    (1593, 1549)]

def word345_3_514 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_512 word345_3_513

def word345_3_515 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 1357 (Flapjack.WordRegImm.reg 1361) word345_3_475 word345_3_514

def word345_3_516 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_438 word345_3_515

def word345_3_517 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_516 word345_0_4

def word345_3_521 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_517 word345_2_865

def word345_3_523 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_521 word345_2_867

def word345_3_525 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_523 word345_2_869

def word345_3_527 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_525 word345_2_871

def word345_3_529 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_527 word345_2_873

def word345_3_531 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_529 word345_2_875

def word345_3_535 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_531 word345_2_879

def word345_3_537 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_535 word345_2_881

def word345_3_541 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_537 word345_2_885

def word345_3_543 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_541 word345_2_887

def word345_3_547 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_543 word345_2_891

def word345_3_549 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_547 word345_2_893

def word345_3_553 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_549 word345_2_897

def word345_3_557 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_553 word345_2_901

def word345_3_559 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_557 word345_2_903

def word345_3_561 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_559 word345_2_905

def word345_3_563 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_561 word345_2_907

def word345_3_565 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_913

def word345_3_567 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_565 word345_2_915

def word345_3_569 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_567 word345_2_921

def word345_3_574 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_925 word345_2_926

def word345_3_577 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_929 word345_2_931

def word345_3_579 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_577 word345_2_935

def word345_3_581 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_579 word345_2_937

def word345_3_582 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_574 word345_3_581

def word345_3_590 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_946 word345_2_948

def word345_3_592 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_590 word345_2_952

def word345_3_594 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_592 word345_2_954

def word345_3_595 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_945 word345_3_594

def word345_3_596 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_3_582, 345, 18)) (some 336) ([2, 4, 6]) (some (2, word345_3_595, 345, 19))

def word345_3_597 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_924 word345_3_596

def word345_3_598 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_923 word345_3_597

def word345_3_599 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_569 word345_3_598

def word345_3_600 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_599 word345_0_4

def word345_3_604 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_600 word345_2_965

def word345_3_606 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_604 word345_2_967

def word345_3_608 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_606 word345_2_969

def word345_3_610 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_608 word345_2_971

def word345_3_612 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_610 word345_2_973

def word345_3_614 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_612 word345_2_975

def word345_3_618 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_614 word345_2_979

def word345_3_620 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_618 word345_2_981

def word345_3_624 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_620 word345_2_985

def word345_3_626 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_624 word345_2_987

def word345_3_630 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_626 word345_2_991

def word345_3_632 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_630 word345_2_993

def word345_3_636 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_632 word345_2_997

def word345_3_640 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_636 word345_2_1001

def word345_3_642 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_640 word345_2_1003

def word345_3_643 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2293, 1765), (2253, 1889), (2249, 1825), (2245, 1777), (2237, 1781)]

def word345_3_644 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_642 word345_3_643

def word345_3_646 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_1012

def word345_3_648 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_646 word345_2_1014

def word345_3_650 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_648 word345_2_1020

def word345_3_655 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1024 word345_2_1025

def word345_3_658 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1028 word345_2_1030

def word345_3_660 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_658 word345_2_1034

def word345_3_662 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_660 word345_2_1036

def word345_3_663 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_655 word345_3_662

def word345_3_671 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1045 word345_2_1047

def word345_3_673 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_671 word345_2_1051

def word345_3_675 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_673 word345_2_1053

def word345_3_676 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1044 word345_3_675

def word345_3_677 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_663, 345, 20)) (some 336) ([2, 4, 6]) (some (2, word345_3_676, 345, 21))

def word345_3_678 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1023 word345_3_677

def word345_3_679 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1022 word345_3_678

def word345_3_680 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_650 word345_3_679

def word345_3_681 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_680 word345_0_4

def word345_3_685 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_681 word345_2_1064

def word345_3_687 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_685 word345_2_1066

def word345_3_689 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_687 word345_2_1068

def word345_3_691 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_689 word345_2_1070

def word345_3_693 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_691 word345_2_1072

def word345_3_695 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_693 word345_2_1074

def word345_3_699 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_695 word345_2_1078

def word345_3_701 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_699 word345_2_1080

def word345_3_705 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_701 word345_2_1084

def word345_3_707 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_705 word345_2_1086

def word345_3_711 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_707 word345_2_1090

def word345_3_713 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_711 word345_2_1092

def word345_3_717 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_713 word345_2_1096

def word345_3_719 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_717 word345_2_1098

def word345_3_723 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_719 word345_2_1102

def word345_3_725 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_723 word345_2_1108

def word345_3_730 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1112 word345_2_1113

def word345_3_733 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1116 word345_2_1118

def word345_3_735 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_733 word345_2_1122

def word345_3_737 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_735 word345_2_1124

def word345_3_738 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_730 word345_3_737

def word345_3_746 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1133 word345_2_1135

def word345_3_748 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_746 word345_2_1139

def word345_3_750 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_748 word345_2_1141

def word345_3_751 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1132 word345_3_750

def word345_3_752 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_738, 345, 22)) (some 336) ([2, 4, 6]) (some (2, word345_3_751, 345, 23))

def word345_3_753 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1111 word345_3_752

def word345_3_754 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1110 word345_3_753

def word345_3_755 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_725 word345_3_754

def word345_3_756 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_755 word345_0_4

def word345_3_760 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_756 word345_2_1152

def word345_3_762 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_760 word345_2_1154

def word345_3_764 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_762 word345_2_1156

def word345_3_766 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_764 word345_2_1158

def word345_3_768 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_766 word345_2_1160

def word345_3_770 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_768 word345_2_1162

def word345_3_774 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_770 word345_2_1166

def word345_3_776 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_774 word345_2_1168

def word345_3_780 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_776 word345_2_1172

def word345_3_782 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_780 word345_2_1174

def word345_3_786 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_782 word345_2_1178

def word345_3_788 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_786 word345_2_1180

def word345_3_792 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_788 word345_2_1184

def word345_3_796 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_792 word345_2_1188

def word345_3_798 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_796 word345_2_1190

def word345_3_799 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2293, 2109), (2253, 2233), (2249, 2169), (2245, 2121), (2237, 2125)]

def word345_3_800 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_798 word345_3_799

def word345_3_801 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1705 (Flapjack.WordRegImm.reg 1709) word345_3_644 word345_3_800

def word345_3_802 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_563 word345_3_801

def word345_3_803 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_802 word345_0_4

def word345_3_805 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_803 word345_2_1198

def word345_3_807 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_805 word345_2_1200

def word345_3_809 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_807 word345_2_1206

def word345_3_811 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_809 word345_2_1208

def word345_3_816 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1212 word345_2_1213

def word345_3_818 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_816 word345_2_1216

def word345_3_825 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1226 word345_2_1227

def word345_3_826 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_3_818, 345, 24)) (some 337) ([2, 4, 6, 8]) (some (2, word345_3_825, 345, 25))

def word345_3_827 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1211 word345_3_826

def word345_3_828 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1210 word345_3_827

def word345_3_829 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_811 word345_3_828

def word345_3_830 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_829 word345_0_4

def word345_3_834 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_830 word345_2_1240

def word345_3_836 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_834 word345_2_1242

def word345_3_838 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_836 word345_2_1244

def word345_3_842 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_838 word345_2_1248

def word345_3_846 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_842 word345_2_1252

def word345_3_848 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_846 word345_2_1254

def word345_3_850 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_848 word345_2_1256

def word345_3_852 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_850 word345_2_1258

def word345_3_854 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_1264

def word345_3_856 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_854 word345_2_1266

def word345_3_858 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_856 word345_2_1272

def word345_3_863 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1276 word345_2_1277

def word345_3_865 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_863 word345_2_1280

def word345_3_872 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1290 word345_2_1291

def word345_3_873 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_3_865, 345, 26)) (some 339) ([2, 4, 6]) (some (2, word345_3_872, 345, 27))

def word345_3_874 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1275 word345_3_873

def word345_3_875 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1274 word345_3_874

def word345_3_876 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_858 word345_3_875

def word345_3_877 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_876 word345_0_4

def word345_3_878 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2613, 2477), (2605, 2481), (2601, 2505), (2597, 2485), (2593, 2489), (2589, 2493)]

def word345_3_879 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_877 word345_3_878

def word345_3_881 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_1309

def word345_3_883 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_881 word345_2_1311

def word345_3_888 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1315 word345_2_1316

def word345_3_890 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_888 word345_2_1319

def word345_3_897 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1329 word345_2_1330

def word345_3_898 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_890, 345, 28)) (some 340) ([2, 4]) (some (2, word345_3_897, 345, 29))

def word345_3_899 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1314 word345_3_898

def word345_3_900 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1313 word345_3_899

def word345_3_901 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_883 word345_3_900

def word345_3_902 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_901 word345_0_4

def word345_3_903 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2613, 2553), (2605, 2557), (2601, 2581), (2597, 2561), (2593, 2565), (2589, 2569)]

def word345_3_904 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_902 word345_3_903

def word345_3_905 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 2417 (Flapjack.WordRegImm.reg 2421) word345_3_879 word345_3_904

def word345_3_906 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_852 word345_3_905

def word345_3_907 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_906 word345_0_4

def word345_3_911 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_907 word345_2_1349

def word345_3_913 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_911 word345_2_1351

def word345_3_915 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_913 word345_2_1353

def word345_3_919 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_915 word345_2_1357

def word345_3_923 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_919 word345_2_1361

def word345_3_925 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_923 word345_2_1363

def word345_3_927 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_925 word345_2_1365

def word345_3_929 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_927 word345_2_1367

def word345_3_931 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_929 word345_2_1371

def word345_3_936 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1375 word345_2_1376

def word345_3_939 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1379 word345_2_1381

def word345_3_941 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_939 word345_2_1385

def word345_3_943 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_941 word345_2_1387

def word345_3_944 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_936 word345_3_943

def word345_3_952 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1396 word345_2_1398

def word345_3_954 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_952 word345_2_1402

def word345_3_956 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_954 word345_2_1404

def word345_3_957 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1395 word345_3_956

def word345_3_958 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_944, 345, 30)) (some 336) ([2, 4, 6]) (some (2, word345_3_957, 345, 31))

def word345_3_959 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1374 word345_3_958

def word345_3_960 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1373 word345_3_959

def word345_3_961 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_931 word345_3_960

def word345_3_962 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_961 word345_0_4

def word345_3_966 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_962 word345_2_1415

def word345_3_968 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_966 word345_2_1417

def word345_3_970 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_968 word345_2_1419

def word345_3_972 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_970 word345_2_1421

def word345_3_974 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_972 word345_2_1423

def word345_3_976 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_974 word345_2_1425

def word345_3_980 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_976 word345_2_1429

def word345_3_982 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_980 word345_2_1431

def word345_3_986 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_982 word345_2_1435

def word345_3_988 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_986 word345_2_1437

def word345_3_992 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_988 word345_2_1441

def word345_3_994 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_992 word345_2_1443

def word345_3_998 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_994 word345_2_1447

def word345_3_1002 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_998 word345_2_1451

def word345_3_1004 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1002 word345_2_1453

def word345_3_1006 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1004 word345_2_1455

def word345_3_1008 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1006 word345_2_1457

def word345_3_1013 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1461 word345_2_1462

def word345_3_1016 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1465 word345_2_1469

def word345_3_1017 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1013 word345_3_1016

def word345_3_1025 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1478 word345_2_1482

def word345_3_1026 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1477 word345_3_1025

def word345_3_1027 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_1017, 345, 32)) (some 338) ([2, 4]) (some (2, word345_3_1026, 345, 33))

def word345_3_1028 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1460 word345_3_1027

def word345_3_1029 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1459 word345_3_1028

def word345_3_1030 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1008 word345_3_1029

def word345_3_1031 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1030 word345_0_4

def word345_3_1035 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1031 word345_2_1493

def word345_3_1037 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1035 word345_2_1495

def word345_3_1039 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1037 word345_2_1497

def word345_3_1043 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1039 word345_2_1501

def word345_3_1047 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1043 word345_2_1505

def word345_3_1049 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1047 word345_2_1507

def word345_3_1051 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1049 word345_2_1509

def word345_3_1055 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1051 word345_2_1513

def word345_3_1059 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1055 word345_2_1517

def word345_3_1061 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1059 word345_2_1519

def word345_3_1063 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1061 word345_2_1521

def word345_3_1065 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1063 word345_2_1523

def word345_3_1067 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_1529

def word345_3_1069 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1067 word345_2_1531

def word345_3_1074 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1535 word345_2_1536

def word345_3_1077 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1539 word345_2_1543

def word345_3_1078 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1074 word345_3_1077

def word345_3_1086 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1552 word345_2_1556

def word345_3_1087 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1551 word345_3_1086

def word345_3_1088 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_3_1078, 345, 34)) (some 341) ([2, 4]) (some (2, word345_3_1087, 345, 35))

def word345_3_1089 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1534 word345_3_1088

def word345_3_1090 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1533 word345_3_1089

def word345_3_1091 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1069 word345_3_1090

def word345_3_1092 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1091 word345_0_4

def word345_3_1094 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1092 word345_2_1565

def word345_3_1096 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1094 word345_2_1567

def word345_3_1101 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1571 word345_2_1572

def word345_3_1104 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1577 word345_2_1579

def word345_3_1105 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1101 word345_3_1104

def word345_3_1113 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1590 word345_2_1592

def word345_3_1114 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1587 word345_3_1113

def word345_3_1115 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_1105, 345, 36)) (some 342) ([2, 4]) (some (2, word345_3_1114, 345, 37))

def word345_3_1116 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1570 word345_3_1115

def word345_3_1117 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1569 word345_3_1116

def word345_3_1118 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1096 word345_3_1117

def word345_3_1119 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1118 word345_0_4

def word345_3_1123 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1119 word345_2_1603

def word345_3_1125 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1123 word345_2_1605

def word345_3_1127 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1125 word345_2_1607

def word345_3_1131 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1127 word345_2_1611

def word345_3_1135 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1131 word345_2_1615

def word345_3_1137 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1135 word345_2_1617

def word345_3_1139 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1137 word345_2_1619

def word345_3_1143 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1139 word345_2_1623

def word345_3_1147 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1143 word345_2_1627

def word345_3_1149 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1147 word345_2_1629

def word345_3_1150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3197, 3069), (3185, 3161), (3181, 3133), (3177, 3081), (3173, 3085)]

def word345_3_1151 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1149 word345_3_1150

def word345_3_1152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3197, 2849), (3185, 2941), (3181, 2913), (3177, 2945), (3173, 2865)]

def word345_3_1153 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_3_1152

def word345_3_1154 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2945 (Flapjack.WordRegImm.reg 2949) word345_3_1151 word345_3_1153

def word345_3_1155 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1065 word345_3_1154

def word345_3_1156 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1155 word345_0_4

def word345_3_1158 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1156 word345_2_1672

def word345_3_1160 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1158 word345_2_1674

def word345_3_1162 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_1680

def word345_3_1164 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1162 word345_2_1682

def word345_3_1166 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1164 word345_2_1688

def word345_3_1171 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1692 word345_2_1693

def word345_3_1174 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1696 word345_2_1698

def word345_3_1176 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1174 word345_2_1702

def word345_3_1178 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1176 word345_2_1704

def word345_3_1179 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1171 word345_3_1178

def word345_3_1187 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1713 word345_2_1715

def word345_3_1189 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1187 word345_2_1719

def word345_3_1191 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1189 word345_2_1721

def word345_3_1192 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1712 word345_3_1191

def word345_3_1193 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln))
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
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_1179, 345, 38)) (some 336) ([2, 4, 6]) (some (2, word345_3_1192, 345, 39))

def word345_3_1194 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1691 word345_3_1193

def word345_3_1195 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1690 word345_3_1194

def word345_3_1196 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1166 word345_3_1195

def word345_3_1197 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1196 word345_0_4

def word345_3_1201 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1197 word345_2_1732

def word345_3_1203 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1201 word345_2_1734

def word345_3_1205 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1203 word345_2_1736

def word345_3_1207 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1205 word345_2_1738

def word345_3_1209 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1207 word345_2_1740

def word345_3_1211 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1209 word345_2_1742

def word345_3_1215 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1211 word345_2_1746

def word345_3_1217 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1215 word345_2_1748

def word345_3_1221 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1217 word345_2_1752

def word345_3_1223 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1221 word345_2_1754

def word345_3_1227 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1223 word345_2_1758

def word345_3_1229 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1227 word345_2_1760

def word345_3_1233 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1229 word345_2_1764

def word345_3_1235 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1233 word345_2_1766

def word345_3_1239 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1235 word345_2_1770

def word345_3_1244 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1774 word345_2_1775

def word345_3_1247 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1778 word345_2_1782

def word345_3_1248 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1244 word345_3_1247

def word345_3_1256 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1791 word345_2_1795

def word345_3_1257 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1790 word345_3_1256

def word345_3_1258 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_3_1248, 345, 40)) (some 341) ([2, 4]) (some (2, word345_3_1257, 345, 41))

def word345_3_1259 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1773 word345_3_1258

def word345_3_1260 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1772 word345_3_1259

def word345_3_1261 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1239 word345_3_1260

def word345_3_1262 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1261 word345_0_4

def word345_3_1264 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1262 word345_2_1804

def word345_3_1266 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1264 word345_2_1806

def word345_3_1271 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1810 word345_2_1811

def word345_3_1274 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1816 word345_2_1818

def word345_3_1275 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1271 word345_3_1274

def word345_3_1283 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1829 word345_2_1831

def word345_3_1284 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1826 word345_3_1283

def word345_3_1285 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_1275, 345, 42)) (some 343) ([2, 4]) (some (2, word345_3_1284, 345, 43))

def word345_3_1286 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1809 word345_3_1285

def word345_3_1287 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1808 word345_3_1286

def word345_3_1288 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1266 word345_3_1287

def word345_3_1289 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1288 word345_0_4

def word345_3_1293 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1289 word345_2_1842

def word345_3_1295 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1293 word345_2_1844

def word345_3_1297 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1295 word345_2_1846

def word345_3_1301 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1297 word345_2_1850

def word345_3_1305 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1301 word345_2_1854

def word345_3_1307 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1305 word345_2_1856

def word345_3_1309 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1307 word345_2_1858

def word345_3_1313 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1309 word345_2_1862

def word345_3_1317 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1313 word345_2_1866

def word345_3_1319 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1317 word345_2_1868

def word345_3_1320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3661, 3521), (3637, 3613), (3633, 3585), (3629, 3533), (3625, 3537)]

def word345_3_1321 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1319 word345_3_1320

def word345_3_1322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3661, 3197), (3637, 3185), (3633, 3181), (3629, 3233), (3625, 3173)]

def word345_3_1323 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_3_1322

def word345_3_1324 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 3233 (Flapjack.WordRegImm.reg 3237) word345_3_1321 word345_3_1323

def word345_3_1325 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1160 word345_3_1324

def word345_3_1326 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1325 word345_0_4

def word345_3_1328 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1326 word345_2_1899

def word345_3_1330 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1328 word345_2_1901

def word345_3_1332 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_2_1907

def word345_3_1334 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1332 word345_2_1909

def word345_3_1339 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1913 word345_2_1914

def word345_3_1342 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1917 word345_2_1921

def word345_3_1343 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1339 word345_3_1342

def word345_3_1351 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1930 word345_2_1934

def word345_3_1352 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1929 word345_3_1351

def word345_3_1353 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word345_3_1343, 345, 44)) (some 341) ([2, 4]) (some (2, word345_3_1352, 345, 45))

def word345_3_1354 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1912 word345_3_1353

def word345_3_1355 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1911 word345_3_1354

def word345_3_1356 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1334 word345_3_1355

def word345_3_1357 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1356 word345_0_4

def word345_3_1359 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1357 word345_2_1943

def word345_3_1361 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1359 word345_2_1945

def word345_3_1366 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1949 word345_2_1950

def word345_3_1369 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1955 word345_2_1957

def word345_3_1370 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1366 word345_3_1369

def word345_3_1378 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1968 word345_2_1970

def word345_3_1379 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1965 word345_3_1378

def word345_3_1380 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_1370, 345, 46)) (some 344) ([2, 4]) (some (2, word345_3_1379, 345, 47))

def word345_3_1381 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1948 word345_3_1380

def word345_3_1382 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_1947 word345_3_1381

def word345_3_1383 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1361 word345_3_1382

def word345_3_1384 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1383 word345_0_4

def word345_3_1388 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1384 word345_2_1981

def word345_3_1390 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1388 word345_2_1983

def word345_3_1392 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1390 word345_2_1985

def word345_3_1396 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1392 word345_2_1989

def word345_3_1400 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1396 word345_2_1993

def word345_3_1402 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1400 word345_2_1995

def word345_3_1404 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1402 word345_2_1997

def word345_3_1408 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1404 word345_2_2001

def word345_3_1412 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1408 word345_2_2005

def word345_3_1414 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1412 word345_2_2007

def word345_3_1415 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3929, 3797), (3905, 3885), (3901, 3857), (3897, 3809)]

def word345_3_1416 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1414 word345_3_1415

def word345_3_1417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3929, 3661), (3905, 3637), (3901, 3633), (3897, 3625)]

def word345_3_1418 : WordLangProgHOL (BitVec 64) :=
.seq word345_0_4 word345_3_1417

def word345_3_1419 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 3685 (Flapjack.WordRegImm.reg 3689) word345_3_1416 word345_3_1418

def word345_3_1420 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1330 word345_3_1419

def word345_3_1421 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1420 word345_0_4

def word345_3_1423 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1421 word345_2_2042

def word345_3_1425 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1423 word345_2_2044

def word345_3_1431 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2051 word345_2_2052

def word345_3_1434 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2055 word345_2_2057

def word345_3_1436 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1434 word345_2_2061

def word345_3_1438 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1436 word345_2_2063

def word345_3_1439 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1431 word345_3_1438

def word345_3_1447 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2072 word345_2_2074

def word345_3_1449 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1447 word345_2_2078

def word345_3_1451 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1449 word345_2_2080

def word345_3_1452 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2071 word345_3_1451

def word345_3_1453 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word345_3_1439, 345, 48)) (some 336) ([2, 4, 6]) (some (2, word345_3_1452, 345, 49))

def word345_3_1454 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2050 word345_3_1453

def word345_3_1455 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2049 word345_3_1454

def word345_3_1456 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2048 word345_3_1455

def word345_3_1457 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1425 word345_3_1456

def word345_3_1458 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1457 word345_0_4

def word345_3_1462 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1458 word345_2_2092

def word345_3_1464 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1462 word345_2_2094

def word345_3_1466 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1464 word345_2_2096

def word345_3_1468 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1466 word345_2_2098

def word345_3_1470 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1468 word345_2_2100

def word345_3_1472 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1470 word345_2_2102

def word345_3_1476 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1472 word345_2_2106

def word345_3_1478 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1476 word345_2_2108

def word345_3_1482 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1478 word345_2_2112

def word345_3_1484 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1482 word345_2_2114

def word345_3_1488 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1484 word345_2_2118

def word345_3_1490 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1488 word345_2_2120

def word345_3_1494 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1490 word345_2_2124

def word345_3_1496 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1494 word345_2_2126

def word345_3_1500 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1496 word345_2_2130

def word345_3_1506 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2137 word345_2_2138

def word345_3_1509 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2141 word345_2_2143

def word345_3_1511 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1509 word345_2_2147

def word345_3_1513 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1511 word345_2_2149

def word345_3_1514 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1506 word345_3_1513

def word345_3_1522 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2158 word345_2_2160

def word345_3_1524 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1522 word345_2_2164

def word345_3_1526 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1524 word345_2_2166

def word345_3_1527 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2157 word345_3_1526

def word345_3_1528 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln
                        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word345_3_1514, 345, 50)) (some 336) ([2, 4, 6]) (some (2, word345_3_1527, 345, 51))

def word345_3_1529 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2136 word345_3_1528

def word345_3_1530 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2135 word345_3_1529

def word345_3_1531 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2134 word345_3_1530

def word345_3_1532 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1500 word345_3_1531

def word345_3_1533 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1532 word345_0_4

def word345_3_1537 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1533 word345_2_2178

def word345_3_1539 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1537 word345_2_2180

def word345_3_1541 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1539 word345_2_2182

def word345_3_1543 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1541 word345_2_2184

def word345_3_1545 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1543 word345_2_2186

def word345_3_1547 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1545 word345_2_2188

def word345_3_1551 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1547 word345_2_2192

def word345_3_1553 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1551 word345_2_2194

def word345_3_1557 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1553 word345_2_2198

def word345_3_1559 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1557 word345_2_2200

def word345_3_1563 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1559 word345_2_2204

def word345_3_1565 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1563 word345_2_2206

def word345_3_1569 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1565 word345_2_2210

def word345_3_1571 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1569 word345_2_2212

def word345_3_1575 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1571 word345_2_2216

def word345_3_1581 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2223 word345_2_2224

def word345_3_1584 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2227 word345_2_2229

def word345_3_1586 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1584 word345_2_2233

def word345_3_1588 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1586 word345_2_2235

def word345_3_1589 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1581 word345_3_1588

def word345_3_1597 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2244 word345_2_2246

def word345_3_1599 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1597 word345_2_2250

def word345_3_1601 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1599 word345_2_2252

def word345_3_1602 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2243 word345_3_1601

def word345_3_1603 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
                  Flapjack.Spt.ln))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)
          Flapjack.Spt.ln))),
  Flapjack.Spt.ln)), word345_3_1589, 345, 52)) (some 336) ([2, 4, 6]) (some (2, word345_3_1602, 345, 53))

def word345_3_1604 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2222 word345_3_1603

def word345_3_1605 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2221 word345_3_1604

def word345_3_1606 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_2220 word345_3_1605

def word345_3_1607 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1575 word345_3_1606

def word345_3_1608 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1607 word345_0_4

def word345_3_1612 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1608 word345_2_2264

def word345_3_1614 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1612 word345_2_2266

def word345_3_1616 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1614 word345_2_2268

def word345_3_1618 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1616 word345_2_2270

def word345_3_1620 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1618 word345_2_2272

def word345_3_1622 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1620 word345_2_2274

def word345_3_1626 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1622 word345_2_2278

def word345_3_1628 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1626 word345_2_2280

def word345_3_1632 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1628 word345_2_2284

def word345_3_1634 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1632 word345_2_2286

def word345_3_1638 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1634 word345_2_2290

def word345_3_1640 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1638 word345_2_2292

def word345_3_1644 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1640 word345_2_2296

def word345_3_1646 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1644 word345_2_2298

def word345_3_1650 : WordLangProgHOL (BitVec 64) :=
.seq word345_3_1646 word345_2_2302

def word345_3_1651 : WordLangProgHOL (BitVec 64) :=
.seq word345_2_0 word345_3_1650

def pass345_3 : WordLangProgHOL (BitVec 64) :=
word345_3_1651
theorem pass345_3_eq : WordAlloc.removeDeadProg (pass345_2) = pass345_3 := by
  kernel_rfl
#print axioms pass345_3_eq
end InitECandidate.Proofs.WordStages
