import InitECandidate.Proofs.Op5.AssemblyInitArena
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyResourceStage

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.WordSemStateFiniteExact

theorem stackLimitLeInitStackWithArena {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C F} (w2 w3 w4 : BitVec width)
    {arena : BitVec width → Prop}
    (hA : labAssumptionsWithArena stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp
      coracle arena)
    (hfmi : fullMakeInitWithArena stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle arena = (sst, some x))
    (h2 : t.regs t.lenReg = .word w2) (h3 : t.regs t.ptr2Reg = .word w3)
    (h4 : t.regs t.len2Reg = .word w4)
    (hlo : w2 + BitVec.ofNat width maxStackAlloc * bytesInWord width ≤ w3)
    (hhi : w3 ≤ w4 - BitVec.ofNat width maxStackAlloc * bytesInWord width)
    (hheap : (-1 * w2 + w3).toNat ≤ maxHeap * (bytesInWord width).toNat)
    (hheapLt : (bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1) (w3 + -1 * w2) = true) :
    (InitLimits.getStackHeapLimit maxHeap (w2, w3, w4)).1 ≤ sst.stack.length := by
  obtain ⟨t', v2, v3, v4, hev, g2, g3, g4, a2, a4, -, tsp2, tsp, tsp1, -⟩ :=
    initCodeRunWithArena hA
  rw [h2] at g2; rw [h3] at g3; rw [h4] at g4
  cases g2; cases g3; cases g4
  obtain ⟨hx, hstack⟩ := fullMakeInitReduceWithArena hfmi hev
  have hgood : goodDimindex width := hA.1
  rw [hstack, hx]
  simp only [initReduceWithArena, withArena, InitReduce.initReduce, length_readMem]
  rw [holFapply_of_lookup tsp, holFapply_of_lookup (tsp1 ⟨hlo, hhi, hheap, hheapLt⟩)]
  exact panToTargetStackLimitLeLength hgood maxHeap w2 w3 w4 a2 a4 hlo hhi hheap hheapLt halign

theorem resourceLimitWithArena {width : Nat} [NeZero width] {C F S Q : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ms : S)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × HolProg width)) (stackMax : Option Nat)
    {sp dataSp : Nat} {offset : BitVec width × BitVec width}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {saveRegs : Nat → Bool}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C F}
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hmax : stackMax = WordDepth.maxDepth wconf.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    {arena : BitVec width → Prop}
    (hA : labAssumptionsWithArena c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
      sp offset bitmaps p t saveRegs dataSp coracle arena)
    (hfmi : fullMakeInitWithArena c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) sp offset bitmaps p t saveRegs dataSp
      coracle arena = (sst, some x))
    (h2 : t.regs t.lenReg = .word (mc.target.getReg ms t.lenReg))
    (h3 : t.regs t.ptr2Reg = .word (mc.target.getReg ms t.ptr2Reg))
    (h4 : t.regs t.len2Reg = .word (mc.target.getReg ms t.len2Reg))
    (hlo : mc.target.getReg ms t.lenReg +
        bytesInWord width * BitVec.ofNat width maxStackAlloc ≤ mc.target.getReg ms t.ptr2Reg)
    (hhi : mc.target.getReg ms t.ptr2Reg ≤
        mc.target.getReg ms t.len2Reg - bytesInWord width * BitVec.ofNat width maxStackAlloc)
    (hheap : (mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg).toNat ≤
        (bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
        2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
        (mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg) = true)
    (hni : WordProps.noInstallCode (sptFromAList wprog))
    (hna : WordProps.noAllocCode (sptFromAList wprog))
    (hnoerr : ∀ k res t',
      evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
          { WordToStack.Native.Initialization.makeInit mc.target.config
              (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
              (sptFromAList wprog) worac with clock := k } = (res, t') →
        res ≠ some WordSemResult.error) :
    optionLt stackMax
        (some (BackendProof.readLimits mc.target.config c mc ms).1) = true →
      WordSemStateFiniteExact.wordLangSafeForSpace
        (WordToStack.Native.Initialization.makeInit mc.target.config
          (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
          (sptFromAList wprog) worac) BvlToBvi.initGlobalsLocation := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, f4, f3, f2, -⟩ := id hA
  have hcomm : mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg =
      -1 * mc.target.getReg ms t.lenReg + mc.target.getReg ms t.ptr2Reg := BitVec.add_comm _ _
  have hle := stackLimitLeInitStackWithArena _ _ _ hA hfmi h2 h3 h4
    (by rwa [BitVec.mul_comm] at hlo) (by rwa [BitVec.mul_comm] at hhi)
    (by rw [← hcomm, Nat.mul_comm]; exact hheap) hheapLt halign
  have hrl : (BackendProof.readLimits mc.target.config c mc ms).1 =
      (InitLimits.getStackHeapLimit (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.getReg ms t.lenReg, mc.target.getReg ms t.ptr2Reg,
          mc.target.getReg ms t.len2Reg)).1 := by
    simp only [BackendProof.readLimits, f2, f3, f4]
  rw [hrl]
  exact panToTargetSafeForSpaceOfLimit mc.target.config sst wprog worac _ _ stackMax
    (by rw [hmax, hwts]) hle hni hna hnoerr

theorem resourceLimitOfSemanticsWithArena {width : Nat} [NeZero width] {C F S Q : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ms : S)
    (panCode : List (Pancake.PanLang.DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × HolProg width)) (stackMax : Option Nat)
    {sp dataSp : Nat} {offset : BitVec width × BitVec width}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} {saveRegs : Nat → Bool}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C F}
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hnodup : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup)
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hmax : stackMax = WordDepth.maxDepth wconf.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    {arena : BitVec width → Prop}
    (hA : labAssumptionsWithArena c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
      sp offset bitmaps p t saveRegs dataSp coracle arena)
    (hfmi : fullMakeInitWithArena c.stackConf c.dataConf
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) sp offset bitmaps p t saveRegs dataSp
      coracle arena = (sst, some x))
    (h2 : t.regs t.lenReg = .word (mc.target.getReg ms t.lenReg))
    (h3 : t.regs t.ptr2Reg = .word (mc.target.getReg ms t.ptr2Reg))
    (h4 : t.regs t.len2Reg = .word (mc.target.getReg ms t.len2Reg))
    (hlo : mc.target.getReg ms t.lenReg +
        bytesInWord width * BitVec.ofNat width maxStackAlloc ≤ mc.target.getReg ms t.ptr2Reg)
    (hhi : mc.target.getReg ms t.ptr2Reg ≤
        mc.target.getReg ms t.len2Reg - bytesInWord width * BitVec.ofNat width maxStackAlloc)
    (hheap : (mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg).toNat ≤
        (bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
        2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
        (mc.target.getReg ms t.ptr2Reg + -1 * mc.target.getReg ms t.lenReg) = true)
    (hsem : WordSemStateFiniteExact.semantics
        (WordToStack.Native.Initialization.makeInit mc.target.config
          (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
          (sptFromAList wprog) worac) BvlToBvi.initGlobalsLocation ≠ .fail) :
    optionLt stackMax
        (some (BackendProof.readLimits mc.target.config c mc ms).1) = true →
      WordSemStateFiniteExact.wordLangSafeForSpace
        (WordToStack.Native.Initialization.makeInit mc.target.config
          (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
          (sptFromAList wprog) worac) BvlToBvi.initGlobalsLocation := by
  obtain ⟨hni, hna⟩ := PanToTarget.word_to_word_compile_no_install_no_alloc c.wordToWordConf
    mc.target.config _ col wprog
    ⟨hwtw, panToWordFirstCompileProgAllDistinctHOL _ panCode hnodup,
      PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl,
      PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl⟩
  exact resourceLimitWithArena c mc ms wprog bitmaps wconf fs p stackMax worac hwts hmax hA
    hfmi h2 h3 h4 hlo hhi hheap hheapLt halign hni
    (hna (PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl))
    (wordNoErrorOfSemanticsNotFail _ _ hsem)

#print axioms resourceLimitOfSemanticsWithArena
end InitE.Op5
