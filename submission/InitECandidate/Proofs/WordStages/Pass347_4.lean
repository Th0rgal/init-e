import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass347_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word347_4_6 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_9

def word347_4_10 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_6 word347_2_13

def word347_4_12 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_10 word347_2_15

def word347_4_16 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_12 word347_2_19

def word347_4_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 77 (Flapjack.WordRegImm.reg 81) word347_4_16 word347_0_16

def word347_4_19 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_18 word347_0_4

def word347_4_20 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_3 word347_4_19

def word347_4_21 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_20 word347_0_4

def word347_4_23 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_21 word347_2_48

def word347_4_25 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_23 word347_2_50

def word347_4_27 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_25 word347_2_52

def word347_4_29 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_27 word347_2_56

def word347_4_34 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_60 word347_2_61

def word347_4_36 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_34 word347_2_65

def word347_4_43 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_75 word347_2_76

def word347_4_44 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_36, 347, 2)) (some 68) ([2]) (some (2, word347_4_43, 347, 3))

def word347_4_45 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_59 word347_4_44

def word347_4_46 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_58 word347_4_45

def word347_4_47 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_29 word347_4_46

def word347_4_48 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_47 word347_0_4

def word347_4_50 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_48 word347_2_87

def word347_4_52 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_50 word347_2_91

def word347_4_61 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_2_95, 347, 4)) (some 78) ([2, 4]) (some (2, word347_2_109, 347, 5))

def word347_4_62 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_94 word347_4_61

def word347_4_63 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_93 word347_4_62

def word347_4_64 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_52 word347_4_63

def word347_4_65 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_64 word347_0_4

def word347_4_69 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_65 word347_2_123

def word347_4_71 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_69 word347_2_125

def word347_4_73 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_71 word347_2_127

def word347_4_77 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_73 word347_2_131

def word347_4_81 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_77 word347_2_135

def word347_4_83 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_81 word347_2_137

def word347_4_85 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_83 word347_2_139

def word347_4_89 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_85 word347_2_143

def word347_4_91 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_89 word347_2_145

def word347_4_93 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_91 word347_2_147

def word347_4_95 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_93 word347_2_149

def word347_4_97 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_95 word347_2_151

def word347_4_99 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_159

def word347_4_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(361, 341)]

def word347_4_101 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_99 word347_4_100

def word347_4_103 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_170

def word347_4_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(361, 357)]

def word347_4_105 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_103 word347_4_104

def word347_4_106 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 321 (Flapjack.WordRegImm.reg 325) word347_4_101 word347_4_105

def word347_4_107 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_97 word347_4_106

def word347_4_108 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_107 word347_0_4

def word347_4_110 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_108 word347_2_178

def word347_4_112 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_110 word347_2_180

def word347_4_114 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_188

def word347_4_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(413, 393)]

def word347_4_116 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_114 word347_4_115

def word347_4_118 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_199

def word347_4_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(413, 409)]

def word347_4_120 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_118 word347_4_119

def word347_4_121 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 373 (Flapjack.WordRegImm.reg 377) word347_4_116 word347_4_120

def word347_4_122 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_112 word347_4_121

def word347_4_123 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_122 word347_0_4

def word347_4_129 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_123 word347_2_211

def word347_4_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(489, 2), (493, 4), (497, 6)]

def word347_4_141 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_222 word347_4_140

def word347_4_144 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_226 word347_2_228

def word347_4_146 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_144 word347_2_232

def word347_4_147 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_141 word347_4_146

def word347_4_155 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_243 word347_2_245

def word347_4_157 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_155 word347_2_249

def word347_4_158 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_242 word347_4_157

def word347_4_159 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_147, 347, 6)) (some 162) ([2, 4]) (some (2, word347_4_158, 347, 7))

def word347_4_160 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_221 word347_4_159

def word347_4_161 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_220 word347_4_160

def word347_4_162 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_219 word347_4_161

def word347_4_163 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_162 word347_0_4

def word347_4_165 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_163 word347_2_260

def word347_4_167 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_165 word347_2_262

def word347_4_169 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_167 word347_2_264

def word347_4_171 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_270

def word347_4_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(569, 549)]

def word347_4_173 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_171 word347_4_172

def word347_4_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(569, 481)]

def word347_4_175 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_4_174

def word347_4_176 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 533 (Flapjack.WordRegImm.reg 537) word347_4_173 word347_4_175

def word347_4_177 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_169 word347_4_176

def word347_4_178 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_177 word347_0_4

def word347_4_180 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_178 word347_2_285

def word347_4_182 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_180 word347_2_287

def word347_4_184 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_293

def word347_4_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(609, 589)]

def word347_4_186 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_184 word347_4_185

def word347_4_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(609, 569)]

def word347_4_188 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_4_187

def word347_4_189 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 573 (Flapjack.WordRegImm.reg 577) word347_4_186 word347_4_188

def word347_4_190 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_182 word347_4_189

def word347_4_191 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_190 word347_0_4

def word347_4_193 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_191 word347_2_308

def word347_4_195 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_193 word347_2_310

def word347_4_197 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_316

def word347_4_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(649, 629)]

def word347_4_199 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_197 word347_4_198

def word347_4_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(649, 609)]

def word347_4_201 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_4_200

def word347_4_202 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 613 (Flapjack.WordRegImm.reg 617) word347_4_199 word347_4_201

def word347_4_203 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_195 word347_4_202

def word347_4_204 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_203 word347_0_4

def word347_4_206 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_204 word347_2_331

def word347_4_208 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_206 word347_2_333

def word347_4_210 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_339

def word347_4_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(689, 669)]

def word347_4_212 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_210 word347_4_211

def word347_4_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(689, 649)]

def word347_4_214 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_4_213

def word347_4_215 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 653 (Flapjack.WordRegImm.reg 657) word347_4_212 word347_4_214

def word347_4_216 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_208 word347_4_215

def word347_4_217 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_216 word347_0_4

def word347_4_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(945, 473), (937, 521), (929, 689), (925, 513), (921, 485), (917, 653), (913, 509)]

def word347_4_219 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_217 word347_4_218

def word347_4_224 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_374

def word347_4_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(733, 713)]

def word347_4_226 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_224 word347_4_225

def word347_4_228 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_385

def word347_4_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(733, 729)]

def word347_4_230 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_228 word347_4_229

def word347_4_231 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 693 (Flapjack.WordRegImm.reg 697) word347_4_226 word347_4_230

def word347_4_232 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_367 word347_4_231

def word347_4_233 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_232 word347_0_4

def word347_4_235 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_233 word347_2_393

def word347_4_237 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_235 word347_2_395

def word347_4_239 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_403

def word347_4_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(785, 765)]

def word347_4_241 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_239 word347_4_240

def word347_4_243 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_414

def word347_4_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(785, 781)]

def word347_4_245 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_243 word347_4_244

def word347_4_246 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 745 (Flapjack.WordRegImm.reg 749) word347_4_241 word347_4_245

def word347_4_247 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_237 word347_4_246

def word347_4_248 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_247 word347_0_4

def word347_4_254 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_248 word347_2_426

def word347_4_265 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 805 (Flapjack.WordRegImm.imm 0#64) word347_0_16 word347_2_442

def word347_4_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(873, 2), (877, 4), (881, 6)]

def word347_4_273 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_454 word347_4_272

def word347_4_276 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_458 word347_2_460

def word347_4_278 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_276 word347_2_464

def word347_4_279 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_273 word347_4_278

def word347_4_287 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_475 word347_2_477

def word347_4_289 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_287 word347_2_481

def word347_4_290 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_474 word347_4_289

def word347_4_291 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_279, 347, 8)) (some 162) ([2, 4]) (some (2, word347_4_290, 347, 9))

def word347_4_292 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_453 word347_4_291

def word347_4_293 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_452 word347_4_292

def word347_4_294 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_451 word347_4_293

def word347_4_295 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_294 word347_0_4

def word347_4_296 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_265 word347_4_295

def word347_4_297 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_254 word347_4_296

def word347_4_298 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_297 word347_0_4

def word347_4_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(945, 857), (937, 905), (929, 861), (925, 897), (921, 865), (917, 869), (913, 893)]

def word347_4_300 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_298 word347_4_299

def word347_4_301 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 433 (Flapjack.WordRegImm.imm 0#64) word347_4_219 word347_4_300

def word347_4_302 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_129 word347_4_301

def word347_4_303 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_302 word347_0_4

def word347_4_305 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_303 word347_2_509

def word347_4_307 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_305 word347_2_511

def word347_4_309 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_307 word347_2_513

def word347_4_313 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_309 word347_2_517

def word347_4_315 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_313 word347_2_519

def word347_4_317 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_315 word347_2_521

def word347_4_319 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_527

def word347_4_323 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_319 word347_2_531

def word347_4_325 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_323 word347_2_533

def word347_4_328 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_325 word347_2_536

def word347_4_329 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 981 (Flapjack.WordRegImm.reg 985) word347_4_328 word347_0_16

def word347_4_330 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_329 word347_0_4

def word347_4_331 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_317 word347_4_330

def word347_4_332 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_331 word347_0_4

def word347_4_334 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_332 word347_2_552

def word347_4_336 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_334 word347_2_554

def word347_4_341 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_558 word347_2_559

def word347_4_344 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_564 word347_2_566

def word347_4_345 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_341 word347_4_344

def word347_4_353 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_577 word347_2_579

def word347_4_354 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_574 word347_4_353

def word347_4_355 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_345, 347, 10)) (some 169) ([2, 4]) (some (2, word347_4_354, 347, 11))

def word347_4_356 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_557 word347_4_355

def word347_4_357 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_556 word347_4_356

def word347_4_358 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_336 word347_4_357

def word347_4_359 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_358 word347_0_4

def word347_4_361 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_359 word347_2_588

def word347_4_363 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_361 word347_2_590

def word347_4_365 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_363 word347_2_592

def word347_4_367 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_598

def word347_4_371 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_367 word347_2_602

def word347_4_373 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_371 word347_2_604

def word347_4_376 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_373 word347_2_607

def word347_4_377 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 1105 (Flapjack.WordRegImm.reg 1109) word347_4_376 word347_0_16

def word347_4_378 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_377 word347_0_4

def word347_4_379 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_365 word347_4_378

def word347_4_380 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_379 word347_0_4

def word347_4_382 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_380 word347_2_635

def word347_4_384 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_382 word347_2_637

def word347_4_386 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_384 word347_2_639

def word347_4_388 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_645

def word347_4_390 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_388 word347_2_659

def word347_4_392 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_390 word347_2_661

def word347_4_394 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_392 word347_2_663

def word347_4_399 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_667 word347_2_668

def word347_4_401 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_399 word347_2_671

def word347_4_408 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_681 word347_2_682

def word347_4_409 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_401, 347, 12)) (some 339) ([2, 4, 6, 8]) (some (2, word347_4_408, 347, 13))

def word347_4_410 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_666 word347_4_409

def word347_4_411 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_665 word347_4_410

def word347_4_412 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_394 word347_4_411

def word347_4_413 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_412 word347_0_4

def word347_4_417 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_413 word347_2_695

def word347_4_419 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_417 word347_2_697

def word347_4_421 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_419 word347_2_699

def word347_4_425 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_421 word347_2_703

def word347_4_427 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_425 word347_2_705

def word347_4_428 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1333, 1237), (1317, 1289), (1309, 1269), (1305, 1245), (1301, 1249)]

def word347_4_429 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_427 word347_4_428

def word347_4_430 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(1333, 1061), (1317, 1157), (1309, 1069), (1305, 1161), (1301, 1101)]

def word347_4_431 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_4_430

def word347_4_432 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 1161 (Flapjack.WordRegImm.reg 1165) word347_4_429 word347_4_431

def word347_4_433 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_386 word347_4_432

def word347_4_434 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_433 word347_0_4

def word347_4_436 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_434 word347_2_736

def word347_4_438 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_436 word347_2_738

def word347_4_440 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_744

def word347_4_442 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_440 word347_2_746

def word347_4_444 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_442 word347_2_756

def word347_4_446 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_444 word347_2_758

def word347_4_451 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_762 word347_2_763

def word347_4_453 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_451 word347_2_766

def word347_4_460 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_776 word347_2_777

def word347_4_461 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_453, 347, 14)) (some 339) ([2, 4, 6, 8]) (some (2, word347_4_460, 347, 15))

def word347_4_462 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_761 word347_4_461

def word347_4_463 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_760 word347_4_462

def word347_4_464 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_446 word347_4_463

def word347_4_465 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_464 word347_0_4

def word347_4_467 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_465 word347_2_788

def word347_4_469 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_467 word347_2_790

def word347_4_471 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_469 word347_2_792

def word347_4_473 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_471 word347_2_794

def word347_4_474 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(1629, 1429), (1625, 1465), (1621, 1473), (1613, 1469), (1609, 1433), (1605, 1437), (1601, 1441), (1597, 1477),
    (1593, 1445)]

def word347_4_475 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_473 word347_4_474

def word347_4_477 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_805

def word347_4_479 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_477 word347_2_807

def word347_4_481 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_479 word347_2_813

def word347_4_486 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_817 word347_2_818

def word347_4_489 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_821 word347_2_823

def word347_4_491 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_489 word347_2_827

def word347_4_493 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_491 word347_2_829

def word347_4_494 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_486 word347_4_493

def word347_4_502 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_838 word347_2_840

def word347_4_504 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_502 word347_2_844

def word347_4_506 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_504 word347_2_846

def word347_4_507 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_837 word347_4_506

def word347_4_508 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_494, 347, 16)) (some 338) ([2, 4, 6]) (some (2, word347_4_507, 347, 17))

def word347_4_509 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_816 word347_4_508

def word347_4_510 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_815 word347_4_509

def word347_4_511 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_481 word347_4_510

def word347_4_512 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_511 word347_0_4

def word347_4_513 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(1629, 1533), (1625, 1589), (1621, 1585), (1613, 1577), (1609, 1537), (1605, 1541), (1601, 1545), (1597, 1573),
    (1593, 1549)]

def word347_4_514 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_512 word347_4_513

def word347_4_515 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 1357 (Flapjack.WordRegImm.reg 1361) word347_4_475 word347_4_514

def word347_4_516 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_438 word347_4_515

def word347_4_517 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_516 word347_0_4

def word347_4_521 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_517 word347_2_865

def word347_4_523 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_521 word347_2_867

def word347_4_525 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_523 word347_2_869

def word347_4_527 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_525 word347_2_871

def word347_4_529 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_527 word347_2_873

def word347_4_531 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_529 word347_2_875

def word347_4_535 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_531 word347_2_879

def word347_4_537 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_535 word347_2_881

def word347_4_541 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_537 word347_2_885

def word347_4_543 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_541 word347_2_887

def word347_4_547 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_543 word347_2_891

def word347_4_549 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_547 word347_2_893

def word347_4_553 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_549 word347_2_897

def word347_4_557 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_553 word347_2_901

def word347_4_559 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_557 word347_2_903

def word347_4_561 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_559 word347_2_905

def word347_4_563 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_561 word347_2_907

def word347_4_565 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_913

def word347_4_567 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_565 word347_2_915

def word347_4_569 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_567 word347_2_921

def word347_4_574 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_925 word347_2_926

def word347_4_577 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_929 word347_2_931

def word347_4_579 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_577 word347_2_935

def word347_4_581 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_579 word347_2_937

def word347_4_582 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_574 word347_4_581

def word347_4_590 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_946 word347_2_948

def word347_4_592 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_590 word347_2_952

def word347_4_594 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_592 word347_2_954

def word347_4_595 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_945 word347_4_594

def word347_4_596 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_582, 347, 18)) (some 338) ([2, 4, 6]) (some (2, word347_4_595, 347, 19))

def word347_4_597 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_924 word347_4_596

def word347_4_598 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_923 word347_4_597

def word347_4_599 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_569 word347_4_598

def word347_4_600 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_599 word347_0_4

def word347_4_604 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_600 word347_2_965

def word347_4_606 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_604 word347_2_967

def word347_4_608 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_606 word347_2_969

def word347_4_610 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_608 word347_2_971

def word347_4_612 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_610 word347_2_973

def word347_4_614 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_612 word347_2_975

def word347_4_618 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_614 word347_2_979

def word347_4_620 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_618 word347_2_981

def word347_4_624 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_620 word347_2_985

def word347_4_626 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_624 word347_2_987

def word347_4_630 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_626 word347_2_991

def word347_4_632 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_630 word347_2_993

def word347_4_636 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_632 word347_2_997

def word347_4_640 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_636 word347_2_1001

def word347_4_642 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_640 word347_2_1003

def word347_4_643 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2293, 1765), (2253, 1889), (2249, 1825), (2245, 1777), (2237, 1781)]

def word347_4_644 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_642 word347_4_643

def word347_4_646 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_1012

def word347_4_648 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_646 word347_2_1014

def word347_4_650 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_648 word347_2_1020

def word347_4_655 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1024 word347_2_1025

def word347_4_658 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1028 word347_2_1030

def word347_4_660 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_658 word347_2_1034

def word347_4_662 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_660 word347_2_1036

def word347_4_663 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_655 word347_4_662

def word347_4_671 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1045 word347_2_1047

def word347_4_673 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_671 word347_2_1051

def word347_4_675 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_673 word347_2_1053

def word347_4_676 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1044 word347_4_675

def word347_4_677 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_663, 347, 20)) (some 338) ([2, 4, 6]) (some (2, word347_4_676, 347, 21))

def word347_4_678 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1023 word347_4_677

def word347_4_679 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1022 word347_4_678

def word347_4_680 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_650 word347_4_679

def word347_4_681 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_680 word347_0_4

def word347_4_685 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_681 word347_2_1064

def word347_4_687 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_685 word347_2_1066

def word347_4_689 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_687 word347_2_1068

def word347_4_691 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_689 word347_2_1070

def word347_4_693 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_691 word347_2_1072

def word347_4_695 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_693 word347_2_1074

def word347_4_699 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_695 word347_2_1078

def word347_4_701 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_699 word347_2_1080

def word347_4_705 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_701 word347_2_1084

def word347_4_707 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_705 word347_2_1086

def word347_4_711 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_707 word347_2_1090

def word347_4_713 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_711 word347_2_1092

def word347_4_717 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_713 word347_2_1096

def word347_4_719 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_717 word347_2_1098

def word347_4_723 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_719 word347_2_1102

def word347_4_725 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_723 word347_2_1108

def word347_4_730 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1112 word347_2_1113

def word347_4_733 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1116 word347_2_1118

def word347_4_735 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_733 word347_2_1122

def word347_4_737 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_735 word347_2_1124

def word347_4_738 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_730 word347_4_737

def word347_4_746 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1133 word347_2_1135

def word347_4_748 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_746 word347_2_1139

def word347_4_750 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_748 word347_2_1141

def word347_4_751 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1132 word347_4_750

def word347_4_752 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_738, 347, 22)) (some 338) ([2, 4, 6]) (some (2, word347_4_751, 347, 23))

def word347_4_753 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1111 word347_4_752

def word347_4_754 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1110 word347_4_753

def word347_4_755 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_725 word347_4_754

def word347_4_756 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_755 word347_0_4

def word347_4_760 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_756 word347_2_1152

def word347_4_762 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_760 word347_2_1154

def word347_4_764 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_762 word347_2_1156

def word347_4_766 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_764 word347_2_1158

def word347_4_768 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_766 word347_2_1160

def word347_4_770 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_768 word347_2_1162

def word347_4_774 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_770 word347_2_1166

def word347_4_776 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_774 word347_2_1168

def word347_4_780 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_776 word347_2_1172

def word347_4_782 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_780 word347_2_1174

def word347_4_786 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_782 word347_2_1178

def word347_4_788 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_786 word347_2_1180

def word347_4_792 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_788 word347_2_1184

def word347_4_796 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_792 word347_2_1188

def word347_4_798 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_796 word347_2_1190

def word347_4_799 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2293, 2109), (2253, 2233), (2249, 2169), (2245, 2121), (2237, 2125)]

def word347_4_800 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_798 word347_4_799

def word347_4_801 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 1705 (Flapjack.WordRegImm.reg 1709) word347_4_644 word347_4_800

def word347_4_802 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_563 word347_4_801

def word347_4_803 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_802 word347_0_4

def word347_4_805 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_803 word347_2_1198

def word347_4_807 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_805 word347_2_1200

def word347_4_809 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_807 word347_2_1206

def word347_4_811 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_809 word347_2_1208

def word347_4_816 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1212 word347_2_1213

def word347_4_818 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_816 word347_2_1216

def word347_4_825 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1226 word347_2_1227

def word347_4_826 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_818, 347, 24)) (some 339) ([2, 4, 6, 8]) (some (2, word347_4_825, 347, 25))

def word347_4_827 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1211 word347_4_826

def word347_4_828 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1210 word347_4_827

def word347_4_829 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_811 word347_4_828

def word347_4_830 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_829 word347_0_4

def word347_4_834 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_830 word347_2_1240

def word347_4_836 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_834 word347_2_1242

def word347_4_838 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_836 word347_2_1244

def word347_4_842 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_838 word347_2_1248

def word347_4_846 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_842 word347_2_1252

def word347_4_848 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_846 word347_2_1254

def word347_4_850 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_848 word347_2_1256

def word347_4_852 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_850 word347_2_1258

def word347_4_854 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_1264

def word347_4_856 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_854 word347_2_1266

def word347_4_858 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_856 word347_2_1272

def word347_4_863 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1276 word347_2_1277

def word347_4_865 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_863 word347_2_1280

def word347_4_872 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1290 word347_2_1291

def word347_4_873 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_865, 347, 26)) (some 341) ([2, 4, 6]) (some (2, word347_4_872, 347, 27))

def word347_4_874 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1275 word347_4_873

def word347_4_875 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1274 word347_4_874

def word347_4_876 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_858 word347_4_875

def word347_4_877 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_876 word347_0_4

def word347_4_878 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2613, 2477), (2605, 2481), (2601, 2505), (2597, 2485), (2593, 2489), (2589, 2493)]

def word347_4_879 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_877 word347_4_878

def word347_4_881 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_1309

def word347_4_883 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_881 word347_2_1311

def word347_4_888 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1315 word347_2_1316

def word347_4_890 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_888 word347_2_1319

def word347_4_897 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1329 word347_2_1330

def word347_4_898 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_890, 347, 28)) (some 342) ([2, 4]) (some (2, word347_4_897, 347, 29))

def word347_4_899 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1314 word347_4_898

def word347_4_900 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1313 word347_4_899

def word347_4_901 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_883 word347_4_900

def word347_4_902 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_901 word347_0_4

def word347_4_903 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2613, 2553), (2605, 2557), (2601, 2581), (2597, 2561), (2593, 2565), (2589, 2569)]

def word347_4_904 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_902 word347_4_903

def word347_4_905 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 2417 (Flapjack.WordRegImm.reg 2421) word347_4_879 word347_4_904

def word347_4_906 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_852 word347_4_905

def word347_4_907 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_906 word347_0_4

def word347_4_911 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_907 word347_2_1349

def word347_4_913 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_911 word347_2_1351

def word347_4_915 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_913 word347_2_1353

def word347_4_919 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_915 word347_2_1357

def word347_4_923 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_919 word347_2_1361

def word347_4_925 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_923 word347_2_1363

def word347_4_927 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_925 word347_2_1365

def word347_4_929 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_927 word347_2_1367

def word347_4_931 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_929 word347_2_1371

def word347_4_936 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1375 word347_2_1376

def word347_4_939 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1379 word347_2_1381

def word347_4_941 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_939 word347_2_1385

def word347_4_943 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_941 word347_2_1387

def word347_4_944 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_936 word347_4_943

def word347_4_952 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1396 word347_2_1398

def word347_4_954 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_952 word347_2_1402

def word347_4_956 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_954 word347_2_1404

def word347_4_957 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1395 word347_4_956

def word347_4_958 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_944, 347, 30)) (some 338) ([2, 4, 6]) (some (2, word347_4_957, 347, 31))

def word347_4_959 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1374 word347_4_958

def word347_4_960 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1373 word347_4_959

def word347_4_961 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_931 word347_4_960

def word347_4_962 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_961 word347_0_4

def word347_4_966 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_962 word347_2_1415

def word347_4_968 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_966 word347_2_1417

def word347_4_970 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_968 word347_2_1419

def word347_4_972 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_970 word347_2_1421

def word347_4_974 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_972 word347_2_1423

def word347_4_976 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_974 word347_2_1425

def word347_4_980 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_976 word347_2_1429

def word347_4_982 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_980 word347_2_1431

def word347_4_986 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_982 word347_2_1435

def word347_4_988 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_986 word347_2_1437

def word347_4_992 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_988 word347_2_1441

def word347_4_994 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_992 word347_2_1443

def word347_4_998 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_994 word347_2_1447

def word347_4_1002 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_998 word347_2_1451

def word347_4_1004 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1002 word347_2_1453

def word347_4_1006 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1004 word347_2_1455

def word347_4_1008 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1006 word347_2_1457

def word347_4_1013 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1461 word347_2_1462

def word347_4_1016 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1465 word347_2_1469

def word347_4_1017 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1013 word347_4_1016

def word347_4_1025 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1478 word347_2_1482

def word347_4_1026 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1477 word347_4_1025

def word347_4_1027 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1017, 347, 32)) (some 340) ([2, 4]) (some (2, word347_4_1026, 347, 33))

def word347_4_1028 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1460 word347_4_1027

def word347_4_1029 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1459 word347_4_1028

def word347_4_1030 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1008 word347_4_1029

def word347_4_1031 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1030 word347_0_4

def word347_4_1035 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1031 word347_2_1493

def word347_4_1037 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1035 word347_2_1495

def word347_4_1039 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1037 word347_2_1497

def word347_4_1043 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1039 word347_2_1501

def word347_4_1047 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1043 word347_2_1505

def word347_4_1049 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1047 word347_2_1507

def word347_4_1051 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1049 word347_2_1509

def word347_4_1055 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1051 word347_2_1513

def word347_4_1059 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1055 word347_2_1517

def word347_4_1061 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1059 word347_2_1519

def word347_4_1063 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1061 word347_2_1521

def word347_4_1065 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1063 word347_2_1523

def word347_4_1067 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_1529

def word347_4_1069 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1067 word347_2_1531

def word347_4_1074 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1535 word347_2_1536

def word347_4_1077 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1539 word347_2_1543

def word347_4_1078 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1074 word347_4_1077

def word347_4_1086 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1552 word347_2_1556

def word347_4_1087 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1551 word347_4_1086

def word347_4_1088 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1078, 347, 34)) (some 343) ([2, 4]) (some (2, word347_4_1087, 347, 35))

def word347_4_1089 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1534 word347_4_1088

def word347_4_1090 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1533 word347_4_1089

def word347_4_1091 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1069 word347_4_1090

def word347_4_1092 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1091 word347_0_4

def word347_4_1094 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1092 word347_2_1565

def word347_4_1096 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1094 word347_2_1567

def word347_4_1101 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1571 word347_2_1572

def word347_4_1104 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1577 word347_2_1579

def word347_4_1105 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1101 word347_4_1104

def word347_4_1113 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1590 word347_2_1592

def word347_4_1114 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1587 word347_4_1113

def word347_4_1115 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1105, 347, 36)) (some 344) ([2, 4]) (some (2, word347_4_1114, 347, 37))

def word347_4_1116 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1570 word347_4_1115

def word347_4_1117 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1569 word347_4_1116

def word347_4_1118 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1096 word347_4_1117

def word347_4_1119 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1118 word347_0_4

def word347_4_1123 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1119 word347_2_1603

def word347_4_1125 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1123 word347_2_1605

def word347_4_1127 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1125 word347_2_1607

def word347_4_1131 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1127 word347_2_1611

def word347_4_1135 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1131 word347_2_1615

def word347_4_1137 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1135 word347_2_1617

def word347_4_1139 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1137 word347_2_1619

def word347_4_1143 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1139 word347_2_1623

def word347_4_1147 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1143 word347_2_1627

def word347_4_1149 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1147 word347_2_1629

def word347_4_1150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3197, 3069), (3185, 3161), (3181, 3133), (3177, 3081), (3173, 3085)]

def word347_4_1151 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1149 word347_4_1150

def word347_4_1152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3197, 2849), (3185, 2941), (3181, 2913), (3177, 2945), (3173, 2865)]

def word347_4_1153 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_4_1152

def word347_4_1154 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2945 (Flapjack.WordRegImm.reg 2949) word347_4_1151 word347_4_1153

def word347_4_1155 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1065 word347_4_1154

def word347_4_1156 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1155 word347_0_4

def word347_4_1158 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1156 word347_2_1672

def word347_4_1160 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1158 word347_2_1674

def word347_4_1162 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_1680

def word347_4_1164 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1162 word347_2_1682

def word347_4_1166 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1164 word347_2_1688

def word347_4_1171 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1692 word347_2_1693

def word347_4_1174 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1696 word347_2_1698

def word347_4_1176 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1174 word347_2_1702

def word347_4_1178 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1176 word347_2_1704

def word347_4_1179 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1171 word347_4_1178

def word347_4_1187 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1713 word347_2_1715

def word347_4_1189 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1187 word347_2_1719

def word347_4_1191 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1189 word347_2_1721

def word347_4_1192 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1712 word347_4_1191

def word347_4_1193 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1179, 347, 38)) (some 338) ([2, 4, 6]) (some (2, word347_4_1192, 347, 39))

def word347_4_1194 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1691 word347_4_1193

def word347_4_1195 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1690 word347_4_1194

def word347_4_1196 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1166 word347_4_1195

def word347_4_1197 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1196 word347_0_4

def word347_4_1201 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1197 word347_2_1732

def word347_4_1203 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1201 word347_2_1734

def word347_4_1205 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1203 word347_2_1736

def word347_4_1207 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1205 word347_2_1738

def word347_4_1209 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1207 word347_2_1740

def word347_4_1211 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1209 word347_2_1742

def word347_4_1215 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1211 word347_2_1746

def word347_4_1217 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1215 word347_2_1748

def word347_4_1221 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1217 word347_2_1752

def word347_4_1223 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1221 word347_2_1754

def word347_4_1227 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1223 word347_2_1758

def word347_4_1229 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1227 word347_2_1760

def word347_4_1233 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1229 word347_2_1764

def word347_4_1235 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1233 word347_2_1766

def word347_4_1239 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1235 word347_2_1770

def word347_4_1244 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1774 word347_2_1775

def word347_4_1247 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1778 word347_2_1782

def word347_4_1248 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1244 word347_4_1247

def word347_4_1256 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1791 word347_2_1795

def word347_4_1257 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1790 word347_4_1256

def word347_4_1258 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1248, 347, 40)) (some 343) ([2, 4]) (some (2, word347_4_1257, 347, 41))

def word347_4_1259 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1773 word347_4_1258

def word347_4_1260 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1772 word347_4_1259

def word347_4_1261 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1239 word347_4_1260

def word347_4_1262 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1261 word347_0_4

def word347_4_1264 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1262 word347_2_1804

def word347_4_1266 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1264 word347_2_1806

def word347_4_1271 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1810 word347_2_1811

def word347_4_1274 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1816 word347_2_1818

def word347_4_1275 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1271 word347_4_1274

def word347_4_1283 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1829 word347_2_1831

def word347_4_1284 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1826 word347_4_1283

def word347_4_1285 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1275, 347, 42)) (some 345) ([2, 4]) (some (2, word347_4_1284, 347, 43))

def word347_4_1286 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1809 word347_4_1285

def word347_4_1287 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1808 word347_4_1286

def word347_4_1288 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1266 word347_4_1287

def word347_4_1289 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1288 word347_0_4

def word347_4_1293 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1289 word347_2_1842

def word347_4_1295 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1293 word347_2_1844

def word347_4_1297 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1295 word347_2_1846

def word347_4_1301 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1297 word347_2_1850

def word347_4_1305 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1301 word347_2_1854

def word347_4_1307 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1305 word347_2_1856

def word347_4_1309 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1307 word347_2_1858

def word347_4_1313 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1309 word347_2_1862

def word347_4_1317 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1313 word347_2_1866

def word347_4_1319 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1317 word347_2_1868

def word347_4_1320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3661, 3521), (3637, 3613), (3633, 3585), (3629, 3533), (3625, 3537)]

def word347_4_1321 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1319 word347_4_1320

def word347_4_1322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3661, 3197), (3637, 3185), (3633, 3181), (3629, 3233), (3625, 3173)]

def word347_4_1323 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_4_1322

def word347_4_1324 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 3233 (Flapjack.WordRegImm.reg 3237) word347_4_1321 word347_4_1323

def word347_4_1325 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1160 word347_4_1324

def word347_4_1326 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1325 word347_0_4

def word347_4_1328 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1326 word347_2_1899

def word347_4_1330 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1328 word347_2_1901

def word347_4_1332 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_2_1907

def word347_4_1334 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1332 word347_2_1909

def word347_4_1339 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1913 word347_2_1914

def word347_4_1342 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1917 word347_2_1921

def word347_4_1343 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1339 word347_4_1342

def word347_4_1351 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1930 word347_2_1934

def word347_4_1352 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1929 word347_4_1351

def word347_4_1353 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1343, 347, 44)) (some 343) ([2, 4]) (some (2, word347_4_1352, 347, 45))

def word347_4_1354 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1912 word347_4_1353

def word347_4_1355 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1911 word347_4_1354

def word347_4_1356 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1334 word347_4_1355

def word347_4_1357 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1356 word347_0_4

def word347_4_1359 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1357 word347_2_1943

def word347_4_1361 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1359 word347_2_1945

def word347_4_1366 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1949 word347_2_1950

def word347_4_1369 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1955 word347_2_1957

def word347_4_1370 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1366 word347_4_1369

def word347_4_1378 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1968 word347_2_1970

def word347_4_1379 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1965 word347_4_1378

def word347_4_1380 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1370, 347, 46)) (some 346) ([2, 4]) (some (2, word347_4_1379, 347, 47))

def word347_4_1381 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1948 word347_4_1380

def word347_4_1382 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_1947 word347_4_1381

def word347_4_1383 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1361 word347_4_1382

def word347_4_1384 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1383 word347_0_4

def word347_4_1388 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1384 word347_2_1981

def word347_4_1390 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1388 word347_2_1983

def word347_4_1392 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1390 word347_2_1985

def word347_4_1396 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1392 word347_2_1989

def word347_4_1400 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1396 word347_2_1993

def word347_4_1402 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1400 word347_2_1995

def word347_4_1404 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1402 word347_2_1997

def word347_4_1408 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1404 word347_2_2001

def word347_4_1412 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1408 word347_2_2005

def word347_4_1414 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1412 word347_2_2007

def word347_4_1415 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3929, 3797), (3905, 3885), (3901, 3857), (3897, 3809)]

def word347_4_1416 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1414 word347_4_1415

def word347_4_1417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3929, 3661), (3905, 3637), (3901, 3633), (3897, 3625)]

def word347_4_1418 : WordLangProgHOL (BitVec 64) :=
.seq word347_0_4 word347_4_1417

def word347_4_1419 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 3685 (Flapjack.WordRegImm.reg 3689) word347_4_1416 word347_4_1418

def word347_4_1420 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1330 word347_4_1419

def word347_4_1421 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1420 word347_0_4

def word347_4_1423 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1421 word347_2_2042

def word347_4_1425 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1423 word347_2_2044

def word347_4_1431 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2051 word347_2_2052

def word347_4_1434 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2055 word347_2_2057

def word347_4_1436 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1434 word347_2_2061

def word347_4_1438 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1436 word347_2_2063

def word347_4_1439 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1431 word347_4_1438

def word347_4_1447 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2072 word347_2_2074

def word347_4_1449 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1447 word347_2_2078

def word347_4_1451 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1449 word347_2_2080

def word347_4_1452 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2071 word347_4_1451

def word347_4_1453 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1439, 347, 48)) (some 338) ([2, 4, 6]) (some (2, word347_4_1452, 347, 49))

def word347_4_1454 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2050 word347_4_1453

def word347_4_1455 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2049 word347_4_1454

def word347_4_1456 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2048 word347_4_1455

def word347_4_1457 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1425 word347_4_1456

def word347_4_1458 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1457 word347_0_4

def word347_4_1462 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1458 word347_2_2092

def word347_4_1464 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1462 word347_2_2094

def word347_4_1466 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1464 word347_2_2096

def word347_4_1468 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1466 word347_2_2098

def word347_4_1470 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1468 word347_2_2100

def word347_4_1472 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1470 word347_2_2102

def word347_4_1476 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1472 word347_2_2106

def word347_4_1478 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1476 word347_2_2108

def word347_4_1482 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1478 word347_2_2112

def word347_4_1484 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1482 word347_2_2114

def word347_4_1488 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1484 word347_2_2118

def word347_4_1490 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1488 word347_2_2120

def word347_4_1494 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1490 word347_2_2124

def word347_4_1496 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1494 word347_2_2126

def word347_4_1500 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1496 word347_2_2130

def word347_4_1506 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2137 word347_2_2138

def word347_4_1509 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2141 word347_2_2143

def word347_4_1511 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1509 word347_2_2147

def word347_4_1513 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1511 word347_2_2149

def word347_4_1514 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1506 word347_4_1513

def word347_4_1522 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2158 word347_2_2160

def word347_4_1524 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1522 word347_2_2164

def word347_4_1526 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1524 word347_2_2166

def word347_4_1527 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2157 word347_4_1526

def word347_4_1528 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1514, 347, 50)) (some 338) ([2, 4, 6]) (some (2, word347_4_1527, 347, 51))

def word347_4_1529 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2136 word347_4_1528

def word347_4_1530 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2135 word347_4_1529

def word347_4_1531 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2134 word347_4_1530

def word347_4_1532 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1500 word347_4_1531

def word347_4_1533 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1532 word347_0_4

def word347_4_1537 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1533 word347_2_2178

def word347_4_1539 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1537 word347_2_2180

def word347_4_1541 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1539 word347_2_2182

def word347_4_1543 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1541 word347_2_2184

def word347_4_1545 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1543 word347_2_2186

def word347_4_1547 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1545 word347_2_2188

def word347_4_1551 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1547 word347_2_2192

def word347_4_1553 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1551 word347_2_2194

def word347_4_1557 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1553 word347_2_2198

def word347_4_1559 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1557 word347_2_2200

def word347_4_1563 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1559 word347_2_2204

def word347_4_1565 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1563 word347_2_2206

def word347_4_1569 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1565 word347_2_2210

def word347_4_1571 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1569 word347_2_2212

def word347_4_1575 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1571 word347_2_2216

def word347_4_1581 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2223 word347_2_2224

def word347_4_1584 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2227 word347_2_2229

def word347_4_1586 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1584 word347_2_2233

def word347_4_1588 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1586 word347_2_2235

def word347_4_1589 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1581 word347_4_1588

def word347_4_1597 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2244 word347_2_2246

def word347_4_1599 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1597 word347_2_2250

def word347_4_1601 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1599 word347_2_2252

def word347_4_1602 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2243 word347_4_1601

def word347_4_1603 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word347_4_1589, 347, 52)) (some 338) ([2, 4, 6]) (some (2, word347_4_1602, 347, 53))

def word347_4_1604 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2222 word347_4_1603

def word347_4_1605 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2221 word347_4_1604

def word347_4_1606 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_2220 word347_4_1605

def word347_4_1607 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1575 word347_4_1606

def word347_4_1608 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1607 word347_0_4

def word347_4_1612 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1608 word347_2_2264

def word347_4_1614 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1612 word347_2_2266

def word347_4_1616 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1614 word347_2_2268

def word347_4_1618 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1616 word347_2_2270

def word347_4_1620 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1618 word347_2_2272

def word347_4_1622 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1620 word347_2_2274

def word347_4_1626 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1622 word347_2_2278

def word347_4_1628 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1626 word347_2_2280

def word347_4_1632 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1628 word347_2_2284

def word347_4_1634 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1632 word347_2_2286

def word347_4_1638 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1634 word347_2_2290

def word347_4_1640 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1638 word347_2_2292

def word347_4_1644 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1640 word347_2_2296

def word347_4_1646 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1644 word347_2_2298

def word347_4_1650 : WordLangProgHOL (BitVec 64) :=
.seq word347_4_1646 word347_2_2302

def word347_4_1651 : WordLangProgHOL (BitVec 64) :=
.seq word347_2_0 word347_4_1650

def pass347_4 : WordLangProgHOL (BitVec 64) :=
word347_4_1651
theorem pass347_4_eq : WordCse.wordCommonSubexpElim (pass347_3) = pass347_4 := by
  kernel_rfl
#print axioms pass347_4_eq
end InitECandidate.Proofs.WordStages
