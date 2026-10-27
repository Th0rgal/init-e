import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass866_3
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word866_4_9 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_7 word866_2_10

def word866_4_14 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_14 word866_2_15

def word866_4_16 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_14 word866_2_20

def word866_4_24 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_31 word866_2_32

def word866_4_25 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_16, 866, 2)) (some 68) ([2]) (some (2, word866_4_24, 866, 3))

def word866_4_26 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_13 word866_4_25

def word866_4_27 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_12 word866_4_26

def word866_4_28 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_9 word866_4_27

def word866_4_30 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_28 word866_0_10

def word866_4_32 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_30 word866_2_44

def word866_4_34 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_32 word866_2_48

def word866_4_43 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_2_52, 866, 4)) (some 78) ([2, 4]) (some (2, word866_2_66, 866, 5))

def word866_4_44 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_51 word866_4_43

def word866_4_45 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_50 word866_4_44

def word866_4_46 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_34 word866_4_45

def word866_4_47 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_46 word866_0_10

def word866_4_49 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_47 word866_2_78

def word866_4_51 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_49 word866_2_82

def word866_4_55 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_51 word866_2_86

def word866_4_59 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_55 word866_2_90

def word866_4_61 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_59 word866_2_92

def word866_4_63 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_61 word866_2_94

def word866_4_67 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_63 word866_2_98

def word866_4_69 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_67 word866_2_102

def word866_4_74 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_106 word866_2_107

def word866_4_76 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_74 word866_2_112

def word866_4_83 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_120 word866_2_123

def word866_4_84 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_76, 866, 6)) (some 68) ([2]) (some (2, word866_4_83, 866, 7))

def word866_4_85 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_105 word866_4_84

def word866_4_86 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_104 word866_4_85

def word866_4_87 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_69 word866_4_86

def word866_4_88 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_87 word866_0_10

def word866_4_90 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_88 word866_2_134

def word866_4_95 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_138 word866_2_139

def word866_4_97 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_95 word866_2_142

def word866_4_104 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_152 word866_2_153

def word866_4_105 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_97, 866, 8)) (some 68) ([2]) (some (2, word866_4_104, 866, 9))

def word866_4_106 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_137 word866_4_105

def word866_4_107 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_136 word866_4_106

def word866_4_108 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_90 word866_4_107

def word866_4_109 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_108 word866_0_10

def word866_4_111 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_109 word866_2_164

def word866_4_113 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_111 word866_2_166

def word866_4_115 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_113 word866_2_168

def word866_4_117 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_115 word866_2_170

def word866_4_119 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_117 word866_2_174

def word866_4_121 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_119 word866_2_176

def word866_4_130 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_2_180, 866, 10)) (some 158) ([2, 4, 6]) (some (2, word866_2_194, 866, 11))

def word866_4_131 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_179 word866_4_130

def word866_4_132 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_178 word866_4_131

def word866_4_133 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_121 word866_4_132

def word866_4_134 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_133 word866_0_10

def word866_4_138 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_134 word866_2_208

def word866_4_140 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_138 word866_2_210

def word866_4_142 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_140 word866_2_212

def word866_4_146 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_142 word866_2_216

def word866_4_150 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_146 word866_2_220

def word866_4_154 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_150 word866_2_224

def word866_4_156 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_154 word866_2_226

def word866_4_160 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_156 word866_2_230

def word866_4_164 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_160 word866_2_234

def word866_4_168 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_164 word866_2_238

def word866_4_170 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_168 word866_2_240

def word866_4_174 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_170 word866_2_244

def word866_4_176 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_174 word866_2_248

def word866_4_181 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_252 word866_2_253

def word866_4_183 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_181 word866_2_258

def word866_4_190 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_266 word866_2_269

def word866_4_191 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_183, 866, 12)) (some 68) ([2]) (some (2, word866_4_190, 866, 13))

def word866_4_192 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_251 word866_4_191

def word866_4_193 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_250 word866_4_192

def word866_4_194 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_176 word866_4_193

def word866_4_195 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_194 word866_0_10

def word866_4_199 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_195 word866_2_280

def word866_4_201 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_199 word866_2_282

def word866_4_203 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_201 word866_2_284

def word866_4_207 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_203 word866_2_288

def word866_4_211 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_207 word866_2_292

def word866_4_215 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_211 word866_2_296

def word866_4_217 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_215 word866_2_298

def word866_4_221 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_217 word866_2_302

def word866_4_225 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_221 word866_2_306

def word866_4_229 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_225 word866_2_310

def word866_4_231 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_229 word866_2_312

def word866_4_235 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_231 word866_2_316

def word866_4_239 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_235 word866_2_320

def word866_4_241 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_239 word866_2_330

def word866_4_245 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_241 word866_2_334

def word866_4_247 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_245 word866_2_336

def word866_4_251 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_247 word866_2_340

def word866_4_253 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_251 word866_2_342

def word866_4_257 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_253 word866_2_346

def word866_4_259 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_257 word866_2_348

def word866_4_263 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_259 word866_2_352

def word866_4_267 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_263 word866_2_356

def word866_4_271 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_267 word866_2_360

def word866_4_273 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_271 word866_2_362

def word866_4_277 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_273 word866_2_366

def word866_4_281 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_277 word866_2_370

def word866_4_285 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_281 word866_2_374

def word866_4_287 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_285 word866_2_376

def word866_4_291 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_287 word866_2_380

def word866_4_295 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_291 word866_2_384

def word866_4_299 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_295 word866_2_388

def word866_4_301 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_299 word866_2_390

def word866_4_305 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_301 word866_2_394

def word866_4_309 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_305 word866_2_398

def word866_4_313 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_309 word866_2_402

def word866_4_315 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_313 word866_2_404

def word866_4_319 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_315 word866_2_408

def word866_4_323 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_319 word866_2_412

def word866_4_327 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_323 word866_2_416

def word866_4_329 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_327 word866_2_418

def word866_4_333 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_329 word866_2_422

def word866_4_337 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_333 word866_2_426

def word866_4_341 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_337 word866_2_430

def word866_4_343 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_341 word866_2_432

def word866_4_347 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_343 word866_2_436

def word866_4_351 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_347 word866_2_440

def word866_4_355 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_351 word866_2_444

def word866_4_357 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_355 word866_2_446

def word866_4_361 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_357 word866_2_450

def word866_4_363 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_361 word866_2_454

def word866_4_368 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_458 word866_2_459

def word866_4_370 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_368 word866_2_462

def word866_4_377 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_472 word866_2_473

def word866_4_378 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_370, 866, 14)) (some 68) ([2]) (some (2, word866_4_377, 866, 15))

def word866_4_379 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_457 word866_4_378

def word866_4_380 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_456 word866_4_379

def word866_4_381 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_363 word866_4_380

def word866_4_382 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_381 word866_0_10

def word866_4_384 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_382 word866_2_484

def word866_4_386 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_384 word866_2_488

def word866_4_395 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_2_492, 866, 16)) (some 78) ([2, 4]) (some (2, word866_2_506, 866, 17))

def word866_4_396 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_491 word866_4_395

def word866_4_397 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_490 word866_4_396

def word866_4_398 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_386 word866_4_397

def word866_4_399 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_398 word866_0_10

def word866_4_403 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_399 word866_2_520

def word866_4_405 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_403 word866_2_522

def word866_4_407 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_405 word866_2_524

def word866_4_411 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_407 word866_2_528

def word866_4_415 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_411 word866_2_532

def word866_4_417 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_415 word866_2_534

def word866_4_421 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_417 word866_2_538

def word866_4_423 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_421 word866_2_540

def word866_4_427 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_423 word866_2_544

def word866_4_429 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_427 word866_2_546

def word866_4_433 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_429 word866_2_550

def word866_4_435 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_433 word866_2_552

def word866_4_439 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_435 word866_2_556

def word866_4_441 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_439 word866_2_558

def word866_4_445 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_441 word866_2_562

def word866_4_447 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_445 word866_2_564

def word866_4_451 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_447 word866_2_568

def word866_4_453 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_451 word866_2_570

def word866_4_457 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_453 word866_2_574

def word866_4_459 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_457 word866_2_576

def word866_4_503 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_459 word866_2_620

def word866_4_507 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_503 word866_2_624

def word866_4_509 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_507 word866_2_626

def word866_4_513 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_509 word866_2_630

def word866_4_515 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_513 word866_2_632

def word866_4_519 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_515 word866_2_636

def word866_4_521 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_519 word866_2_638

def word866_4_525 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_521 word866_2_642

def word866_4_527 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_525 word866_2_644

def word866_4_531 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_527 word866_2_648

def word866_4_533 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_531 word866_2_650

def word866_4_537 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_533 word866_2_654

def word866_4_539 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_537 word866_2_656

def word866_4_543 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_539 word866_2_660

def word866_4_545 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_543 word866_2_662

def word866_4_549 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_545 word866_2_666

def word866_4_551 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_549 word866_2_668

def word866_4_595 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_551 word866_2_712

def word866_4_599 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_595 word866_2_716

def word866_4_601 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_599 word866_2_718

def word866_4_605 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_601 word866_2_722

def word866_4_607 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_605 word866_2_724

def word866_4_611 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_607 word866_2_728

def word866_4_613 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_611 word866_2_730

def word866_4_617 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_613 word866_2_734

def word866_4_619 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_617 word866_2_736

def word866_4_623 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_619 word866_2_740

def word866_4_625 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_623 word866_2_742

def word866_4_629 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_625 word866_2_746

def word866_4_631 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_629 word866_2_748

def word866_4_635 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_631 word866_2_752

def word866_4_637 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_635 word866_2_754

def word866_4_641 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_637 word866_2_758

def word866_4_643 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_641 word866_2_760

def word866_4_687 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_643 word866_2_804

def word866_4_691 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_687 word866_2_808

def word866_4_693 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_691 word866_2_810

def word866_4_697 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_693 word866_2_814

def word866_4_699 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_697 word866_2_816

def word866_4_703 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_699 word866_2_820

def word866_4_705 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_703 word866_2_822

def word866_4_709 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_705 word866_2_826

def word866_4_711 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_709 word866_2_828

def word866_4_715 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_711 word866_2_832

def word866_4_717 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_715 word866_2_834

def word866_4_721 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_717 word866_2_838

def word866_4_723 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_721 word866_2_840

def word866_4_727 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_723 word866_2_844

def word866_4_729 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_727 word866_2_846

def word866_4_733 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_729 word866_2_850

def word866_4_735 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_733 word866_2_852

def word866_4_779 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_735 word866_2_896

def word866_4_783 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_779 word866_2_900

def word866_4_785 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_783 word866_2_902

def word866_4_787 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_785 word866_2_904

def word866_4_789 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_787 word866_2_906

def word866_4_791 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_789 word866_2_908

def word866_4_793 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_791 word866_2_910

def word866_4_797 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_793 word866_2_914

def word866_4_799 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_797 word866_2_916

def word866_4_803 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_799 word866_2_920

def word866_4_805 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_803 word866_2_922

def word866_4_809 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_805 word866_2_926

def word866_4_811 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_809 word866_2_928

def word866_4_815 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_811 word866_2_932

def word866_4_817 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_815 word866_2_936

def word866_4_822 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_940 word866_2_941

def word866_4_824 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_822 word866_2_944

def word866_4_831 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_954 word866_2_955

def word866_4_832 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_824, 866, 18)) (some 68) ([2]) (some (2, word866_4_831, 866, 19))

def word866_4_833 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_939 word866_4_832

def word866_4_834 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_938 word866_4_833

def word866_4_835 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_817 word866_4_834

def word866_4_836 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_835 word866_0_10

def word866_4_840 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_836 word866_2_968

def word866_4_842 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_840 word866_2_970

def word866_4_844 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_842 word866_2_972

def word866_4_848 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_844 word866_2_976

def word866_4_852 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_848 word866_2_980

def word866_4_856 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_852 word866_2_984

def word866_4_858 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_856 word866_2_986

def word866_4_862 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_858 word866_2_990

def word866_4_866 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_862 word866_2_994

def word866_4_870 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_866 word866_2_998

def word866_4_872 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_870 word866_2_1000

def word866_4_876 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_872 word866_2_1004

def word866_4_880 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_876 word866_2_1008

def word866_4_884 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_880 word866_2_1012

def word866_4_886 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_884 word866_2_1014

def word866_4_890 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_886 word866_2_1018

def word866_4_892 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_890 word866_2_1022

def word866_4_897 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1026 word866_2_1027

def word866_4_899 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_897 word866_2_1032

def word866_4_906 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1040 word866_2_1043

def word866_4_907 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_899, 866, 20)) (some 68) ([2]) (some (2, word866_4_906, 866, 21))

def word866_4_908 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1025 word866_4_907

def word866_4_909 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1024 word866_4_908

def word866_4_910 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_892 word866_4_909

def word866_4_911 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_910 word866_0_10

def word866_4_915 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_911 word866_2_1054

def word866_4_917 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_915 word866_2_1056

def word866_4_919 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_917 word866_2_1058

def word866_4_923 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_919 word866_2_1062

def word866_4_925 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_923 word866_2_1066

def word866_4_930 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1070 word866_2_1071

def word866_4_932 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_930 word866_2_1074

def word866_4_939 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1084 word866_2_1085

def word866_4_940 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_932, 866, 22)) (some 68) ([2]) (some (2, word866_4_939, 866, 23))

def word866_4_941 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1069 word866_4_940

def word866_4_942 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1068 word866_4_941

def word866_4_943 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_925 word866_4_942

def word866_4_944 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_943 word866_0_10

def word866_4_948 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_944 word866_2_1098

def word866_4_950 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_948 word866_2_1100

def word866_4_952 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_950 word866_2_1102

def word866_4_956 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_952 word866_2_1106

def word866_4_960 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_956 word866_2_1110

def word866_4_964 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_960 word866_2_1114

def word866_4_966 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_964 word866_2_1116

def word866_4_970 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_966 word866_2_1120

def word866_4_972 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_970 word866_2_1122

def word866_4_974 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_972 word866_2_1124

def word866_4_979 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1128 word866_2_1129

def word866_4_981 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_979 word866_2_1132

def word866_4_988 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1142 word866_2_1143

def word866_4_989 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_981, 866, 24)) (some 865) ([2, 4]) (some (2, word866_4_988, 866, 25))

def word866_4_990 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1127 word866_4_989

def word866_4_991 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1126 word866_4_990

def word866_4_992 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_974 word866_4_991

def word866_4_993 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_992 word866_0_10

def word866_4_995 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_993 word866_2_1154

def word866_4_997 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_995 word866_2_1156

def word866_4_999 : WordLangProgHOL (BitVec 64) :=
.seq word866_0_10 word866_2_1162

def word866_4_1003 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_999 word866_2_1166

def word866_4_1005 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1003 word866_2_1168

def word866_4_1008 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1005 word866_2_1171

def word866_4_1010 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 2737 (Flapjack.WordRegImm.reg 2741) word866_4_1008 word866_0_6

def word866_4_1011 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1010 word866_0_10

def word866_4_1012 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_997 word866_4_1011

def word866_4_1013 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1012 word866_0_10

def word866_4_1017 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1013 word866_2_1197

def word866_4_1021 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1017 word866_2_1201

def word866_4_1023 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1021 word866_2_1203

def word866_4_1032 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_2_1207, 866, 26)) (some 334) ([2, 4, 6]) (some (2, word866_2_1221, 866, 27))

def word866_4_1033 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1206 word866_4_1032

def word866_4_1034 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1205 word866_4_1033

def word866_4_1035 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1023 word866_4_1034

def word866_4_1036 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1035 word866_0_10

def word866_4_1040 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1036 word866_2_1235

def word866_4_1046 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1040 word866_2_1241

def word866_4_1051 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1245 word866_2_1246

def word866_4_1053 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1051 word866_2_1249

def word866_4_1060 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1259 word866_2_1260

def word866_4_1061 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_1053, 866, 28)) (some 68) ([2]) (some (2, word866_4_1060, 866, 29))

def word866_4_1062 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1244 word866_4_1061

def word866_4_1063 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1243 word866_4_1062

def word866_4_1064 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1046 word866_4_1063

def word866_4_1065 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1064 word866_0_10

def word866_4_1073 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1065 word866_2_1277

def word866_4_1075 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1073 word866_2_1279

def word866_4_1077 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1075 word866_2_1281

def word866_4_1081 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1077 word866_2_1285

def word866_4_1083 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1081 word866_2_1287

def word866_4_1084 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1083 word866_0_10

def word866_4_1090 : WordLangProgHOL (BitVec 64) :=
.seq word866_0_10 word866_2_1299

def word866_4_1092 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1090 word866_2_1301

def word866_4_1095 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3285, 0)]

def word866_4_1096 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1304 word866_4_1095

def word866_4_1097 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1303 word866_4_1096

def word866_4_1098 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1092 word866_4_1097

def word866_4_1106 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1098 word866_2_1315

def word866_4_1111 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1319 word866_2_1320

def word866_4_1114 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1325 word866_2_1327

def word866_4_1115 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1111 word866_4_1114

def word866_4_1123 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1338 word866_2_1340

def word866_4_1124 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1335 word866_4_1123

def word866_4_1125 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_1115, 866, 30)) (some 857) ([2]) (some (2, word866_4_1124, 866, 31))

def word866_4_1126 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1318 word866_4_1125

def word866_4_1127 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1317 word866_4_1126

def word866_4_1128 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1106 word866_4_1127

def word866_4_1129 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1128 word866_0_10

def word866_4_1143 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1129 word866_2_1361

def word866_4_1145 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1143 word866_2_1363

def word866_4_1147 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1145 word866_2_1365

def word866_4_1151 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1147 word866_2_1369

def word866_4_1153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3529, 3489)]

def word866_4_1154 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1371 word866_4_1153

def word866_4_1155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(3533, 3493)]

def word866_4_1156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3537, 3497)]

def word866_4_1157 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1155 word866_4_1156

def word866_4_1158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(3541, 3501)]

def word866_4_1159 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1157 word866_4_1158

def word866_4_1161 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1159 word866_2_1379

def word866_4_1163 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1161 word866_2_1381

def word866_4_1164 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1154 word866_4_1163

def word866_4_1166 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1164 word866_2_1384

def word866_4_1167 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1151 word866_4_1166

def word866_4_1169 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1167 word866_2_1387

def word866_4_1171 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1169 word866_2_1389

def word866_4_1175 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1171 word866_2_1393

def word866_4_1179 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1175 word866_2_1397

def word866_4_1181 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1179 word866_2_1399

def word866_4_1185 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1181 word866_2_1403

def word866_4_1186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(3673, 3385), (3669, 3389), (3665, 3393), (3661, 3397), (3657, 3401), (3649, 3405), (3645, 3409), (3641, 3413),
    (3633, 3417), (3629, 3421), (3625, 3425), (3621, 3429), (3617, 3433), (3613, 3437), (3609, 3577), (3605, 3445),
    (3597, 3449), (3593, 3453), (3589, 3457)]

def word866_4_1187 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1185 word866_4_1186

def word866_4_1191 : WordLangProgHOL (BitVec 64) :=
.seq word866_0_10 word866_2_1422

def word866_4_1192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1
  [(3673, 3181), (3669, 3261), (3665, 3189), (3661, 3193), (3657, 3197), (3649, 3201), (3645, 3205), (3641, 3209),
    (3633, 3213), (3629, 3217), (3625, 3221), (3621, 3225), (3617, 3229), (3613, 3233), (3609, 3257), (3605, 3241),
    (3597, 3245), (3593, 3249), (3589, 3253)]

def word866_4_1193 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1191 word866_4_1192

def word866_4_1194 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 3257 (Flapjack.WordRegImm.reg 3261) word866_4_1187 word866_4_1193

def word866_4_1195 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1294 word866_4_1194

def word866_4_1196 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1195 word866_0_10

def word866_4_1198 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1196 word866_2_1438

def word866_4_1199 : WordLangProgHOL (BitVec 64) :=
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
    Flapjack.Spt.ln)) word866_4_1198 (Flapjack.Spt.bn Flapjack.Spt.ln
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

def word866_4_1200 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1290 word866_4_1199

def word866_4_1201 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1084 word866_4_1200

def word866_4_1202 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1201 word866_0_10

def word866_4_1210 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1202 word866_2_1450

def word866_4_1212 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1210 word866_2_1452

def word866_4_1214 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1212 word866_2_1454

def word866_4_1223 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_2_1458, 866, 32)) (some 334) ([2, 4, 6]) (some (2, word866_2_1472, 866, 33))

def word866_4_1224 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1457 word866_4_1223

def word866_4_1225 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1456 word866_4_1224

def word866_4_1226 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1214 word866_4_1225

def word866_4_1227 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1226 word866_0_10

def word866_4_1231 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1227 word866_2_1486

def word866_4_1236 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1490 word866_2_1491

def word866_4_1239 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1496 word866_2_1498

def word866_4_1240 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1236 word866_4_1239

def word866_4_1248 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1509 word866_2_1511

def word866_4_1249 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1506 word866_4_1248

def word866_4_1250 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_4_1240, 866, 34)) (some 858) ([2]) (some (2, word866_4_1249, 866, 35))

def word866_4_1251 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1489 word866_4_1250

def word866_4_1252 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1488 word866_4_1251

def word866_4_1253 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1231 word866_4_1252

def word866_4_1254 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1253 word866_0_10

def word866_4_1256 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1254 word866_2_1520

def word866_4_1258 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1256 word866_2_1522

def word866_4_1260 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1258 word866_2_1524

def word866_4_1269 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_2_1528, 866, 36)) (some 859) ([2, 4, 6]) (some (2, word866_2_1542, 866, 37))

def word866_4_1270 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1527 word866_4_1269

def word866_4_1271 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1526 word866_4_1270

def word866_4_1272 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1260 word866_4_1271

def word866_4_1273 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1272 word866_0_10

def word866_4_1277 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1273 word866_2_1556

def word866_4_1281 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1277 word866_2_1560

def word866_4_1283 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1281 word866_2_1562

def word866_4_1292 : WordLangProgHOL (BitVec 64) :=
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
  Flapjack.Spt.ln)), word866_2_1566, 866, 38)) (some 158) ([2, 4, 6]) (some (2, word866_2_1580, 866, 39))

def word866_4_1293 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1565 word866_4_1292

def word866_4_1294 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_1564 word866_4_1293

def word866_4_1295 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1283 word866_4_1294

def word866_4_1296 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1295 word866_0_10

def word866_4_1298 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1296 word866_2_1592

def word866_4_1302 : WordLangProgHOL (BitVec 64) :=
.seq word866_4_1298 word866_2_1596

def word866_4_1303 : WordLangProgHOL (BitVec 64) :=
.seq word866_2_0 word866_4_1302

def pass866_4 : WordLangProgHOL (BitVec 64) :=
word866_4_1303
theorem pass866_4_eq : WordCse.wordCommonSubexpElim (pass866_3) = pass866_4 := by
  kernel_rfl
#print axioms pass866_4_eq
end InitECandidate.Proofs.WordStages
