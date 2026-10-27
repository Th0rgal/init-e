import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.WordStages.Pass341_8
import InitECandidate.Proofs.CompilerComputation
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.CompilerComputation
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Proofs.WordStages
def proposed341 : Option (Spt Nat) :=
some
  (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls 3) 1 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 4))) 0
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 3) Flapjack.Spt.ln) 1
            (Flapjack.Spt.bs (Flapjack.Spt.ls 0) 1 Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 1 (Flapjack.Spt.bs Flapjack.Spt.ln 4 (Flapjack.Spt.ls 0)))
            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 1)))))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls 2) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 1))) 0
            (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.ls 2)))
          (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln 2 (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0)))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 0))))))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls 22)) Flapjack.Spt.ln)))))
def word341_9_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(4, 4), (0, 0), (2, 2)]

def word341_9_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.shift Flapjack.Shift.lsl 4 4 (Flapjack.WordRegImm.imm 4#64)))

def word341_9_292 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 2)]

def word341_9_293 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.binop Flapjack.BinOp.add 4 4 (Flapjack.WordRegImm.reg 2)))

def word341_9_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 2 (Flapjack.WordLangAddr.addr 4 0#64))

def word341_9_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(4, 4)]

def word341_9_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load 4 (Flapjack.WordLangAddr.addr 4 8#64))

def word341_9_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (4, 4), (44, 0)]

def word341_9_298 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(6, 6), (4, 4), (0, 2), (8, 44)]

def word341_9_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2), (8, 44)]

def word341_9_300 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_299 word341_2_123

def word341_9_301 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 4, 6, 8]), ((Flapjack.Spt.bn
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls ())) Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), word341_9_298, 341, 2)) (some 161) ([2, 4]) (some (2, word341_9_300, 341, 3))

def word341_9_302 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(0, 0)]

def word341_9_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 1#64)

def word341_9_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 0 18#64)

def word341_9_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 0)

def word341_9_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.const 2 6#64)

def word341_9_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 1 [(2, 2)]

def word341_9_308 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_307 word341_2_123

def word341_9_309 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_306 word341_9_308

def word341_9_310 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_305 word341_9_309

def word341_9_311 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_302 word341_9_310

def word341_9_312 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_304 word341_9_311

def word341_9_313 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_9_312

def word341_9_314 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 0 (Flapjack.WordRegImm.reg 2) word341_9_313 word341_0_3

def word341_9_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.move 0 [(2, 4), (4, 6)]

def word341_9_316 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 8 [2, 4]

def word341_9_317 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_315 word341_9_316

def word341_9_318 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_9_317

def word341_9_319 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_9_318

def word341_9_320 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_314 word341_9_319

def word341_9_321 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_303 word341_9_320

def word341_9_322 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_302 word341_9_321

def word341_9_323 : WordLangProgHOL (BitVec 64) :=
.seq word341_0_7 word341_9_322

def word341_9_324 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_301 word341_9_323

def word341_9_325 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_297 word341_9_324

def word341_9_326 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_296 word341_9_325

def word341_9_327 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_295 word341_9_326

def word341_9_328 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_294 word341_9_327

def word341_9_329 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_293 word341_9_328

def word341_9_330 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_292 word341_9_329

def word341_9_331 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_291 word341_9_330

def word341_9_332 : WordLangProgHOL (BitVec 64) :=
.seq word341_9_290 word341_9_331

def pass341_9 : WordLangProgHOL (BitVec 64) :=
word341_9_332
theorem pass341_9_eq : WordToWord.wordAllocWith RegAlloc.regAllocExecutable 341 riscvConfig RiscVConfig.pancakeRiscVBackendConfig.wordToWordConf.regAlg (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) (pass341_8) proposed341 = pass341_9 := by
  kernel_rfl
#print axioms pass341_9_eq
end InitECandidate.Proofs.WordStages
