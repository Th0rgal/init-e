import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass854_2
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word854_3_9 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_7 word854_2_10

def word854_3_14 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_14 word854_2_15

def word854_3_16 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_14 word854_2_20

def word854_3_24 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_31 word854_2_32

def word854_3_25 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word854_3_16, 854, 2)) (some 68) ([2]) (some (2, word854_3_24, 854, 3))

def word854_3_26 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_13 word854_3_25

def word854_3_27 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_12 word854_3_26

def word854_3_28 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_9 word854_3_27

def word854_3_30 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_28 word854_0_10

def word854_3_32 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_30 word854_2_44

def word854_3_34 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_32 word854_2_48

def word854_3_43 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word854_2_52, 854, 4)) (some 78) ([2, 4]) (some (2, word854_2_66, 854, 5))

def word854_3_44 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_51 word854_3_43

def word854_3_45 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_50 word854_3_44

def word854_3_46 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_34 word854_3_45

def word854_3_47 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_46 word854_0_10

def word854_3_49 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_47 word854_2_78

def word854_3_51 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_49 word854_2_82

def word854_3_55 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_51 word854_2_86

def word854_3_59 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_55 word854_2_90

def word854_3_61 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_59 word854_2_92

def word854_3_63 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_61 word854_2_94

def word854_3_67 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_63 word854_2_98

def word854_3_69 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_67 word854_2_102

def word854_3_74 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_106 word854_2_107

def word854_3_76 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_74 word854_2_112

def word854_3_83 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_120 word854_2_123

def word854_3_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word854_3_76, 854, 6)) (some 68) ([2]) (some (2, word854_3_83, 854, 7))

def word854_3_85 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_105 word854_3_84

def word854_3_86 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_104 word854_3_85

def word854_3_87 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_69 word854_3_86

def word854_3_88 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_87 word854_0_10

def word854_3_90 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_88 word854_2_134

def word854_3_95 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_138 word854_2_139

def word854_3_97 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_95 word854_2_142

def word854_3_104 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_152 word854_2_153

def word854_3_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word854_3_97, 854, 8)) (some 68) ([2]) (some (2, word854_3_104, 854, 9))

def word854_3_106 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_137 word854_3_105

def word854_3_107 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_136 word854_3_106

def word854_3_108 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_90 word854_3_107

def word854_3_109 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_108 word854_0_10

def word854_3_111 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_109 word854_2_164

def word854_3_113 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_111 word854_2_166

def word854_3_115 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_113 word854_2_168

def word854_3_117 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_115 word854_2_170

def word854_3_119 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_117 word854_2_174

def word854_3_121 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_119 word854_2_176

def word854_3_130 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word854_2_180, 854, 10)) (some 158) ([2, 4, 6]) (some (2, word854_2_194, 854, 11))

def word854_3_131 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_179 word854_3_130

def word854_3_132 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_178 word854_3_131

def word854_3_133 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_121 word854_3_132

def word854_3_134 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_133 word854_0_10

def word854_3_138 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_134 word854_2_208

def word854_3_140 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_138 word854_2_210

def word854_3_142 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_140 word854_2_212

def word854_3_146 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_142 word854_2_216

def word854_3_150 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_146 word854_2_220

def word854_3_154 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_150 word854_2_224

def word854_3_156 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_154 word854_2_226

def word854_3_160 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_156 word854_2_230

def word854_3_164 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_160 word854_2_234

def word854_3_168 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_164 word854_2_238

def word854_3_170 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_168 word854_2_240

def word854_3_174 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_170 word854_2_244

def word854_3_176 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_174 word854_2_248

def word854_3_181 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_252 word854_2_253

def word854_3_183 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_181 word854_2_258

def word854_3_190 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_266 word854_2_269

def word854_3_191 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word854_3_183, 854, 12)) (some 68) ([2]) (some (2, word854_3_190, 854, 13))

def word854_3_192 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_251 word854_3_191

def word854_3_193 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_250 word854_3_192

def word854_3_194 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_176 word854_3_193

def word854_3_195 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_194 word854_0_10

def word854_3_199 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_195 word854_2_280

def word854_3_201 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_199 word854_2_282

def word854_3_203 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_201 word854_2_284

def word854_3_207 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_203 word854_2_288

def word854_3_211 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_207 word854_2_292

def word854_3_215 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_211 word854_2_296

def word854_3_217 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_215 word854_2_298

def word854_3_221 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_217 word854_2_302

def word854_3_225 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_221 word854_2_306

def word854_3_229 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_225 word854_2_310

def word854_3_231 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_229 word854_2_312

def word854_3_235 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_231 word854_2_316

def word854_3_239 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_235 word854_2_320

def word854_3_241 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_239 word854_2_330

def word854_3_245 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_241 word854_2_334

def word854_3_247 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_245 word854_2_336

def word854_3_251 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_247 word854_2_340

def word854_3_253 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_251 word854_2_342

def word854_3_257 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_253 word854_2_346

def word854_3_259 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_257 word854_2_348

def word854_3_263 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_259 word854_2_352

def word854_3_267 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_263 word854_2_356

def word854_3_271 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_267 word854_2_360

def word854_3_273 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_271 word854_2_362

def word854_3_277 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_273 word854_2_366

def word854_3_281 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_277 word854_2_370

def word854_3_285 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_281 word854_2_374

def word854_3_287 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_285 word854_2_376

def word854_3_291 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_287 word854_2_380

def word854_3_295 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_291 word854_2_384

def word854_3_299 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_295 word854_2_388

def word854_3_301 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_299 word854_2_390

def word854_3_305 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_301 word854_2_394

def word854_3_309 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_305 word854_2_398

def word854_3_313 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_309 word854_2_402

def word854_3_315 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_313 word854_2_404

def word854_3_319 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_315 word854_2_408

def word854_3_323 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_319 word854_2_412

def word854_3_327 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_323 word854_2_416

def word854_3_329 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_327 word854_2_418

def word854_3_333 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_329 word854_2_422

def word854_3_337 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_333 word854_2_426

def word854_3_341 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_337 word854_2_430

def word854_3_343 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_341 word854_2_432

def word854_3_347 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_343 word854_2_436

def word854_3_351 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_347 word854_2_440

def word854_3_355 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_351 word854_2_444

def word854_3_357 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_355 word854_2_446

def word854_3_361 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_357 word854_2_450

def word854_3_363 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_361 word854_2_454

def word854_3_368 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_458 word854_2_459

def word854_3_370 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_368 word854_2_462

def word854_3_377 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_472 word854_2_473

def word854_3_378 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))))),
  Flapjack.Spt.ln)), word854_3_370, 854, 14)) (some 68) ([2]) (some (2, word854_3_377, 854, 15))

def word854_3_379 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_457 word854_3_378

def word854_3_380 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_456 word854_3_379

def word854_3_381 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_363 word854_3_380

def word854_3_382 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_381 word854_0_10

def word854_3_384 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_382 word854_2_484

def word854_3_386 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_384 word854_2_488

def word854_3_395 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word854_2_492, 854, 16)) (some 78) ([2, 4]) (some (2, word854_2_506, 854, 17))

def word854_3_396 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_491 word854_3_395

def word854_3_397 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_490 word854_3_396

def word854_3_398 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_386 word854_3_397

def word854_3_399 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_398 word854_0_10

def word854_3_403 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_399 word854_2_520

def word854_3_405 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_403 word854_2_522

def word854_3_407 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_405 word854_2_524

def word854_3_411 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_407 word854_2_528

def word854_3_415 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_411 word854_2_532

def word854_3_417 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_415 word854_2_534

def word854_3_421 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_417 word854_2_538

def word854_3_423 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_421 word854_2_540

def word854_3_427 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_423 word854_2_544

def word854_3_429 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_427 word854_2_546

def word854_3_433 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_429 word854_2_550

def word854_3_435 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_433 word854_2_552

def word854_3_439 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_435 word854_2_556

def word854_3_441 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_439 word854_2_558

def word854_3_445 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_441 word854_2_562

def word854_3_447 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_445 word854_2_564

def word854_3_451 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_447 word854_2_568

def word854_3_453 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_451 word854_2_570

def word854_3_457 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_453 word854_2_574

def word854_3_459 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_457 word854_2_576

def word854_3_503 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_459 word854_2_620

def word854_3_507 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_503 word854_2_624

def word854_3_509 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_507 word854_2_626

def word854_3_513 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_509 word854_2_630

def word854_3_515 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_513 word854_2_632

def word854_3_519 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_515 word854_2_636

def word854_3_521 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_519 word854_2_638

def word854_3_525 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_521 word854_2_642

def word854_3_527 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_525 word854_2_644

def word854_3_531 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_527 word854_2_648

def word854_3_533 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_531 word854_2_650

def word854_3_537 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_533 word854_2_654

def word854_3_539 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_537 word854_2_656

def word854_3_543 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_539 word854_2_660

def word854_3_545 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_543 word854_2_662

def word854_3_549 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_545 word854_2_666

def word854_3_551 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_549 word854_2_668

def word854_3_595 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_551 word854_2_712

def word854_3_599 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_595 word854_2_716

def word854_3_601 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_599 word854_2_718

def word854_3_605 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_601 word854_2_722

def word854_3_607 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_605 word854_2_724

def word854_3_611 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_607 word854_2_728

def word854_3_613 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_611 word854_2_730

def word854_3_617 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_613 word854_2_734

def word854_3_619 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_617 word854_2_736

def word854_3_623 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_619 word854_2_740

def word854_3_625 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_623 word854_2_742

def word854_3_629 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_625 word854_2_746

def word854_3_631 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_629 word854_2_748

def word854_3_635 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_631 word854_2_752

def word854_3_637 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_635 word854_2_754

def word854_3_641 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_637 word854_2_758

def word854_3_643 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_641 word854_2_760

def word854_3_687 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_643 word854_2_804

def word854_3_691 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_687 word854_2_808

def word854_3_693 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_691 word854_2_810

def word854_3_697 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_693 word854_2_814

def word854_3_699 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_697 word854_2_816

def word854_3_703 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_699 word854_2_820

def word854_3_705 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_703 word854_2_822

def word854_3_709 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_705 word854_2_826

def word854_3_711 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_709 word854_2_828

def word854_3_715 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_711 word854_2_832

def word854_3_717 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_715 word854_2_834

def word854_3_721 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_717 word854_2_838

def word854_3_723 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_721 word854_2_840

def word854_3_727 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_723 word854_2_844

def word854_3_729 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_727 word854_2_846

def word854_3_733 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_729 word854_2_850

def word854_3_735 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_733 word854_2_852

def word854_3_779 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_735 word854_2_896

def word854_3_783 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_779 word854_2_900

def word854_3_785 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_783 word854_2_902

def word854_3_787 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_785 word854_2_904

def word854_3_789 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_787 word854_2_906

def word854_3_791 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_789 word854_2_908

def word854_3_793 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_791 word854_2_910

def word854_3_797 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_793 word854_2_914

def word854_3_799 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_797 word854_2_916

def word854_3_803 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_799 word854_2_920

def word854_3_805 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_803 word854_2_922

def word854_3_809 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_805 word854_2_926

def word854_3_811 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_809 word854_2_928

def word854_3_815 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_811 word854_2_932

def word854_3_817 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_815 word854_2_936

def word854_3_822 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_940 word854_2_941

def word854_3_824 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_822 word854_2_944

def word854_3_831 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_954 word854_2_955

def word854_3_832 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln
                      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))))))),
  Flapjack.Spt.ln)), word854_3_824, 854, 18)) (some 68) ([2]) (some (2, word854_3_831, 854, 19))

def word854_3_833 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_939 word854_3_832

def word854_3_834 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_938 word854_3_833

def word854_3_835 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_817 word854_3_834

def word854_3_836 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_835 word854_0_10

def word854_3_840 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_836 word854_2_968

def word854_3_842 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_840 word854_2_970

def word854_3_844 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_842 word854_2_972

def word854_3_848 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_844 word854_2_976

def word854_3_852 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_848 word854_2_980

def word854_3_856 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_852 word854_2_984

def word854_3_858 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_856 word854_2_986

def word854_3_862 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_858 word854_2_990

def word854_3_866 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_862 word854_2_994

def word854_3_870 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_866 word854_2_998

def word854_3_872 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_870 word854_2_1000

def word854_3_876 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_872 word854_2_1004

def word854_3_880 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_876 word854_2_1008

def word854_3_884 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_880 word854_2_1012

def word854_3_886 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_884 word854_2_1014

def word854_3_890 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_886 word854_2_1018

def word854_3_892 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_890 word854_2_1022

def word854_3_897 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1026 word854_2_1027

def word854_3_899 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_897 word854_2_1032

def word854_3_906 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1040 word854_2_1043

def word854_3_907 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word854_3_899, 854, 20)) (some 68) ([2]) (some (2, word854_3_906, 854, 21))

def word854_3_908 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1025 word854_3_907

def word854_3_909 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1024 word854_3_908

def word854_3_910 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_892 word854_3_909

def word854_3_911 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_910 word854_0_10

def word854_3_915 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_911 word854_2_1054

def word854_3_917 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_915 word854_2_1056

def word854_3_919 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_917 word854_2_1058

def word854_3_923 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_919 word854_2_1062

def word854_3_925 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_923 word854_2_1066

def word854_3_930 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1070 word854_2_1071

def word854_3_932 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_930 word854_2_1074

def word854_3_939 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1084 word854_2_1085

def word854_3_940 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))))))),
  Flapjack.Spt.ln)), word854_3_932, 854, 22)) (some 68) ([2]) (some (2, word854_3_939, 854, 23))

def word854_3_941 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1069 word854_3_940

def word854_3_942 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1068 word854_3_941

def word854_3_943 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_925 word854_3_942

def word854_3_944 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_943 word854_0_10

def word854_3_948 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_944 word854_2_1098

def word854_3_950 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_948 word854_2_1100

def word854_3_952 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_950 word854_2_1102

def word854_3_956 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_952 word854_2_1106

def word854_3_960 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_956 word854_2_1110

def word854_3_964 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_960 word854_2_1114

def word854_3_966 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_964 word854_2_1116

def word854_3_970 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_966 word854_2_1120

def word854_3_972 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_970 word854_2_1122

def word854_3_974 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_972 word854_2_1124

def word854_3_979 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1128 word854_2_1129

def word854_3_981 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_979 word854_2_1132

def word854_3_988 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1142 word854_2_1143

def word854_3_989 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word854_3_981, 854, 24)) (some 853) ([2, 4]) (some (2, word854_3_988, 854, 25))

def word854_3_990 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1127 word854_3_989

def word854_3_991 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1126 word854_3_990

def word854_3_992 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_974 word854_3_991

def word854_3_993 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_992 word854_0_10

def word854_3_995 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_993 word854_2_1154

def word854_3_997 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_995 word854_2_1156

def word854_3_999 : WordLangProgHOL (BitVec 64) :=
.seq word854_0_10 word854_2_1162

def word854_3_1003 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_999 word854_2_1166

def word854_3_1005 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1003 word854_2_1168

def word854_3_1008 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1005 word854_2_1171

def word854_3_1010 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 2737 (Flapjack.WordRegImm.reg 2741) word854_3_1008 word854_0_6

def word854_3_1011 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1010 word854_0_10

def word854_3_1012 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_997 word854_3_1011

def word854_3_1013 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1012 word854_0_10

def word854_3_1017 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1013 word854_2_1197

def word854_3_1021 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1017 word854_2_1201

def word854_3_1023 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1021 word854_2_1203

def word854_3_1032 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
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
                    Flapjack.Spt.ln)))))
          (Flapjack.Spt.bn
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
                    Flapjack.Spt.ln))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
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
                    Flapjack.Spt.ln)))))
          (Flapjack.Spt.bn
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
                    Flapjack.Spt.ln)))))))),
  Flapjack.Spt.ln)), word854_2_1207, 854, 26)) (some 332) ([2, 4, 6]) (some (2, word854_2_1221, 854, 27))

def word854_3_1033 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1206 word854_3_1032

def word854_3_1034 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1205 word854_3_1033

def word854_3_1035 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1023 word854_3_1034

def word854_3_1036 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1035 word854_0_10

def word854_3_1040 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1036 word854_2_1235

def word854_3_1046 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1040 word854_2_1241

def word854_3_1051 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1245 word854_2_1246

def word854_3_1053 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1051 word854_2_1249

def word854_3_1060 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1259 word854_2_1260

def word854_3_1061 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
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
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
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
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
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
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln))
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
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)))))),
  Flapjack.Spt.ln)), word854_3_1053, 854, 28)) (some 68) ([2]) (some (2, word854_3_1060, 854, 29))

def word854_3_1062 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1244 word854_3_1061

def word854_3_1063 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1243 word854_3_1062

def word854_3_1064 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1046 word854_3_1063

def word854_3_1065 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1064 word854_0_10

def word854_3_1073 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1065 word854_2_1277

def word854_3_1075 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1073 word854_2_1279

def word854_3_1077 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1075 word854_2_1281

def word854_3_1081 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1077 word854_2_1285

def word854_3_1083 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1081 word854_2_1287

def word854_3_1084 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1083 word854_0_10

def word854_3_1090 : WordLangProgHOL (BitVec 64) :=
.seq word854_0_10 word854_2_1299

def word854_3_1092 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1090 word854_2_1301

def word854_3_1095 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3285, 0)]

def word854_3_1096 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1304 word854_3_1095

def word854_3_1097 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1303 word854_3_1096

def word854_3_1098 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1092 word854_3_1097

def word854_3_1106 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1098 word854_2_1315

def word854_3_1111 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1319 word854_2_1320

def word854_3_1114 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1325 word854_2_1327

def word854_3_1115 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1111 word854_3_1114

def word854_3_1123 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1338 word854_2_1340

def word854_3_1124 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1335 word854_3_1123

def word854_3_1125 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
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
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
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
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
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
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln))))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
                    Flapjack.Spt.ln)))))))),
  Flapjack.Spt.ln)), word854_3_1115, 854, 30)) (some 845) ([2]) (some (2, word854_3_1124, 854, 31))

def word854_3_1126 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1318 word854_3_1125

def word854_3_1127 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1317 word854_3_1126

def word854_3_1128 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1106 word854_3_1127

def word854_3_1129 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1128 word854_0_10

def word854_3_1143 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1129 word854_2_1361

def word854_3_1145 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1143 word854_2_1363

def word854_3_1147 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1145 word854_2_1365

def word854_3_1151 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1147 word854_2_1369

def word854_3_1167 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1151 word854_2_1385

def word854_3_1169 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1167 word854_2_1387

def word854_3_1171 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1169 word854_2_1389

def word854_3_1175 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1171 word854_2_1393

def word854_3_1179 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1175 word854_2_1397

def word854_3_1181 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1179 word854_2_1399

def word854_3_1185 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1181 word854_2_1403

def word854_3_1186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(3673, 3385), (3669, 3389), (3665, 3393), (3661, 3397), (3657, 3401), (3649, 3405), (3645, 3409), (3641, 3413),
    (3633, 3417), (3629, 3421), (3625, 3425), (3621, 3429), (3617, 3433), (3613, 3437), (3609, 3577), (3605, 3445),
    (3597, 3449), (3593, 3453), (3589, 3457)]

def word854_3_1187 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1185 word854_3_1186

def word854_3_1191 : WordLangProgHOL (BitVec 64) :=
.seq word854_0_10 word854_2_1422

def word854_3_1192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(3673, 3181), (3669, 3261), (3665, 3189), (3661, 3193), (3657, 3197), (3649, 3201), (3645, 3205), (3641, 3209),
    (3633, 3213), (3629, 3217), (3625, 3221), (3621, 3225), (3617, 3229), (3613, 3233), (3609, 3257), (3605, 3241),
    (3597, 3245), (3593, 3249), (3589, 3253)]

def word854_3_1193 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1191 word854_3_1192

def word854_3_1194 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 3257 (Flapjack.WordRegImm.reg 3261) word854_3_1187 word854_3_1193

def word854_3_1195 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1294 word854_3_1194

def word854_3_1196 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1195 word854_0_10

def word854_3_1198 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1196 word854_2_1438

def word854_3_1199 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))))))
    Flapjack.Spt.ln)) word854_3_1198 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              Flapjack.Spt.ln)
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln)))
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          Flapjack.Spt.ln)))
    Flapjack.Spt.ln))

def word854_3_1200 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1290 word854_3_1199

def word854_3_1201 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1084 word854_3_1200

def word854_3_1202 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1201 word854_0_10

def word854_3_1210 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1202 word854_2_1450

def word854_3_1212 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1210 word854_2_1452

def word854_3_1214 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1212 word854_2_1454

def word854_3_1223 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))
            Flapjack.Spt.ln))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln))))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)))
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word854_2_1458, 854, 32)) (some 332) ([2, 4, 6]) (some (2, word854_2_1472, 854, 33))

def word854_3_1224 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1457 word854_3_1223

def word854_3_1225 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1456 word854_3_1224

def word854_3_1226 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1214 word854_3_1225

def word854_3_1227 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1226 word854_0_10

def word854_3_1231 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1227 word854_2_1486

def word854_3_1236 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1490 word854_2_1491

def word854_3_1239 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1496 word854_2_1498

def word854_3_1240 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1236 word854_3_1239

def word854_3_1248 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1509 word854_2_1511

def word854_3_1249 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1506 word854_3_1248

def word854_3_1250 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn Flapjack.Spt.ln
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln))
            Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn
                  (Flapjack.Spt.bn Flapjack.Spt.ln
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
                  Flapjack.Spt.ln)
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))))),
  Flapjack.Spt.ln)), word854_3_1240, 854, 34)) (some 846) ([2]) (some (2, word854_3_1249, 854, 35))

def word854_3_1251 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1489 word854_3_1250

def word854_3_1252 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1488 word854_3_1251

def word854_3_1253 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1231 word854_3_1252

def word854_3_1254 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1253 word854_0_10

def word854_3_1256 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1254 word854_2_1520

def word854_3_1258 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1256 word854_2_1522

def word854_3_1260 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1258 word854_2_1524

def word854_3_1269 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln))
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn Flapjack.Spt.ln
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln)))
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word854_2_1528, 854, 36)) (some 847) ([2, 4, 6]) (some (2, word854_2_1542, 854, 37))

def word854_3_1270 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1527 word854_3_1269

def word854_3_1271 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1526 word854_3_1270

def word854_3_1272 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1260 word854_3_1271

def word854_3_1273 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1272 word854_0_10

def word854_3_1277 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1273 word854_2_1556

def word854_3_1281 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1277 word854_2_1560

def word854_3_1283 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1281 word854_2_1562

def word854_3_1292 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln))
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn
            (Flapjack.Spt.bn
              (Flapjack.Spt.bn
                (Flapjack.Spt.bn Flapjack.Spt.ln
                  (Flapjack.Spt.bn
                    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
                    Flapjack.Spt.ln))
                Flapjack.Spt.ln)
              Flapjack.Spt.ln)
            Flapjack.Spt.ln)))),
  Flapjack.Spt.ln)), word854_2_1566, 854, 38)) (some 158) ([2, 4, 6]) (some (2, word854_2_1580, 854, 39))

def word854_3_1293 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1565 word854_3_1292

def word854_3_1294 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_1564 word854_3_1293

def word854_3_1295 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1283 word854_3_1294

def word854_3_1296 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1295 word854_0_10

def word854_3_1298 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1296 word854_2_1592

def word854_3_1302 : WordLangProgHOL (BitVec 64) :=
.seq word854_3_1298 word854_2_1596

def word854_3_1303 : WordLangProgHOL (BitVec 64) :=
.seq word854_2_0 word854_3_1302

def pass854_3 : WordLangProgHOL (BitVec 64) :=
word854_3_1303
theorem pass854_3_eq : WordAlloc.removeDeadProg (pass854_2) = pass854_3 := by
  kernel_rfl
#print axioms pass854_3_eq
end InitECandidate.Proofs.WordStages
