import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.SmallSsaKernelComputation
import InitECandidate.Proofs.WordStages.Pass270_1
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def word270_2_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(25, 0), (29, 2), (33, 4)]

def word270_2_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(37, 29)]

def word270_2_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(41, 33)]

def word270_2_156 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_154 word270_2_155

def word270_2_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 45 0#64)

def word270_2_158 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_156 word270_2_157

def word270_2_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 49 0#64)

def word270_2_160 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_158 word270_2_159

def word270_2_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(55, 25), (59, 41), (63, 37)]

def word270_2_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 37), (4, 41), (6, 49)]

def word270_2_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(69, 55), (73, 59), (77, 63)]

def word270_2_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(81, 2), (85, 4)]

def word270_2_165 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_164 word270_0_6

def word270_2_166 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_163 word270_2_165

def word270_2_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 []

def word270_2_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(93, 81)]

def word270_2_169 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_6 word270_2_168

def word270_2_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(97, 85)]

def word270_2_171 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_169 word270_2_170

def word270_2_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 101 0#64)

def word270_2_173 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_171 word270_2_172

def word270_2_174 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_167 word270_2_173

def word270_2_175 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_166 word270_2_174

def word270_2_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(89, 2)]

def word270_2_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 89)]

def word270_2_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def word270_2_179 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_177 word270_2_178

def word270_2_180 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_176 word270_2_179

def word270_2_181 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_163 word270_2_180

def word270_2_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 93 0#64)

def word270_2_183 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_6 word270_2_182

def word270_2_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 97 0#64)

def word270_2_185 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_183 word270_2_184

def word270_2_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(101, 89)]

def word270_2_187 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_185 word270_2_186

def word270_2_188 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_167 word270_2_187

def word270_2_189 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_181 word270_2_188

def word270_2_190 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4]), ((Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls ()) Flapjack.Spt.ln)
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())))))),
  Flapjack.Spt.ln)), word270_2_175, 270, 2)) (some 269) ([2, 4, 6]) (some (2, word270_2_189, 270, 3))

def word270_2_191 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_162 word270_2_190

def word270_2_192 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_161 word270_2_191

def word270_2_193 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_160 word270_2_192

def word270_2_194 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_193 word270_0_10

def word270_2_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 105 8#64)

def word270_2_196 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_194 word270_2_195

def word270_2_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(109, 97)]

def word270_2_198 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_196 word270_2_197

def word270_2_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 113 1#64)

def word270_2_200 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_199 word270_0_10

def word270_2_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 117 1#64)

def word270_2_202 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_200 word270_2_201

def word270_2_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 121 4#64)

def word270_2_204 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_202 word270_2_203

def word270_2_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(125, 121)]

def word270_2_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 125)

def word270_2_207 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_205 word270_2_206

def word270_2_208 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_204 word270_2_207

def word270_2_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 129 3#64)

def word270_2_210 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_208 word270_2_209

def word270_2_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 129)]

def word270_2_212 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_211 word270_2_178

def word270_2_213 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_210 word270_2_212

def word270_2_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(137, 129), (133, 113)]

def word270_2_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(141, 117)]

def word270_2_216 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_6 word270_2_215

def word270_2_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(145, 125)]

def word270_2_218 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_216 word270_2_217

def word270_2_219 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_214 word270_2_218

def word270_2_220 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_213 word270_2_219

def word270_2_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 2 [(137, 101), (133, 105)]

def word270_2_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 141 0#64)

def word270_2_223 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_6 word270_2_222

def word270_2_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 145 0#64)

def word270_2_225 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_223 word270_2_224

def word270_2_226 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_221 word270_2_225

def word270_2_227 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_6 word270_2_226

def word270_2_228 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 105 (Flapjack.WordRegImm.reg 109) word270_2_220 word270_2_227

def word270_2_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 149 0#64)

def word270_2_230 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_229 word270_0_10

def word270_2_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 153 0#64)

def word270_2_232 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_230 word270_2_231

def word270_2_233 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_228 word270_2_232

def word270_2_234 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_198 word270_2_233

def word270_2_235 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_234 word270_0_10

def word270_2_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 157 0#64)

def word270_2_237 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_235 word270_2_236

def word270_2_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 161 0#64)

def word270_2_239 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_237 word270_2_238

def word270_2_240 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_239 word270_0_10

def word270_2_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(165, 69), (169, 157), (173, 109), (177, 73), (181, 161), (185, 77), (189, 93)]

def word270_2_242 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_6 word270_2_241

def word270_2_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(193, 181)]

def word270_2_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(197, 173)]

def word270_2_245 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_243 word270_2_244

def word270_2_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 201 1#64)

def word270_2_247 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_246 word270_0_10

def word270_2_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 205 1#64)

def word270_2_249 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_247 word270_2_248

def word270_2_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(209, 193)]

def word270_2_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(213, 189)]

def word270_2_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 217 209 (Flapjack.WordRegImm.reg 213)))

def word270_2_253 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_251 word270_2_252

def word270_2_254 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_250 word270_2_253

def word270_2_255 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_249 word270_2_254

def word270_2_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 221 (Flapjack.WordLangAddr.addr 217 0#64))

def word270_2_257 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_255 word270_2_256

def word270_2_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(225, 221)]

def word270_2_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(229, 169)]

def word270_2_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 233 229 (Flapjack.WordRegImm.imm 8#64)))

def word270_2_261 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_259 word270_2_260

def word270_2_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.or 237 225 (Flapjack.WordRegImm.reg 233)))

def word270_2_263 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_261 word270_2_262

def word270_2_264 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_258 word270_2_263

def word270_2_265 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_257 word270_2_264

def word270_2_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(241, 237)]

def word270_2_267 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_265 word270_2_266

def word270_2_268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(245, 209)]

def word270_2_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 249 245 (Flapjack.WordRegImm.imm 1#64)))

def word270_2_270 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_268 word270_2_269

def word270_2_271 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_267 word270_2_270

def word270_2_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(253, 249)]

def word270_2_273 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_271 word270_2_272

def word270_2_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(169, 241), (173, 197), (181, 253), (189, 213)]

def word270_2_275 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_274 word270_0_57

def word270_2_276 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_273 word270_2_275

def word270_2_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(281, 241), (277, 253), (273, 213), (269, 205), (265, 241)]

def word270_2_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(285, 233)]

def word270_2_279 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_6 word270_2_278

def word270_2_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(289, 253)]

def word270_2_281 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_279 word270_2_280

def word270_2_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(293, 245)]

def word270_2_283 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_281 word270_2_282

def word270_2_284 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_277 word270_2_283

def word270_2_285 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_276 word270_2_284

def word270_2_286 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 257 0#64)

def word270_2_287 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_286 word270_0_10

def word270_2_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 261 0#64)

def word270_2_289 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_287 word270_2_288

def word270_2_290 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_289 word270_0_62

def word270_2_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(281, 169), (277, 193), (273, 189), (269, 261), (265, 257)]

def word270_2_292 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 285 0#64)

def word270_2_293 : WordLangProgHOL (BitVec 64) :=
.seq word270_0_6 word270_2_292

def word270_2_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 289 0#64)

def word270_2_295 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_293 word270_2_294

def word270_2_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 293 0#64)

def word270_2_297 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_295 word270_2_296

def word270_2_298 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_291 word270_2_297

def word270_2_299 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_290 word270_2_298

def word270_2_300 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 193 (Flapjack.WordRegImm.reg 197) word270_2_285 word270_2_299

def word270_2_301 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_245 word270_2_300

def word270_2_302 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_301 word270_0_10

def word270_2_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(169, 281), (173, 197), (181, 277), (189, 273)]

def word270_2_304 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_302 word270_2_303

def word270_2_305 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
          Flapjack.Spt.ln)))
    Flapjack.Spt.ln)) word270_2_304 (Flapjack.Spt.bn Flapjack.Spt.ln
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln))
        Flapjack.Spt.ln))
    Flapjack.Spt.ln))

def word270_2_306 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_242 word270_2_305

def word270_2_307 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_240 word270_2_306

def word270_2_308 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_307 word270_0_10

def word270_2_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(297, 169)]

def word270_2_310 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_308 word270_2_309

def word270_2_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 297)]

def word270_2_312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 165 [2]

def word270_2_313 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_311 word270_2_312

def word270_2_314 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_310 word270_2_313

def word270_2_315 : WordLangProgHOL (BitVec 64) :=
.seq word270_2_153 word270_2_314

def pass270_2 : WordLangProgHOL (BitVec 64) :=
word270_2_315
theorem pass270_2_eq : WordAlloc.fullSsaCcTrans 3 (pass270_1) = pass270_2 := by
  rw [InitECandidate.Proofs.SmallSsaKernelComputation.fullSsaStructural_eq]
  kernel_rfl
#print axioms pass270_2_eq
end InitECandidate.Proofs.WordStages
