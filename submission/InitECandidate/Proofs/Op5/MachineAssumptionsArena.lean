import InitECandidate.Proofs.Op5.MachineMemoryArena
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyWordToStack

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend.LabToTarget
open Classical

theorem fullMakeInitAssumptionsWithArena {width : Nat} [NeZero width] {S Q F C : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState F)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltc : C)
    (panCode : List (DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (dataSp : Nat) (byteArena : BitVec width → Bool) (arena : BitVec width → Prop)
    (wordArenaEq : ∀ a, arena a ↔ byteArena a = true ∧ holByteAligned a = true)
    (arenaHeap : ∀ a, arena a → ¬(t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ a ∧
      a < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)))
    (arenaBitmap : ∀ a, arena a → bitmapsDm a ≠ true)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, c'', fs, p))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup) :
    let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let biw := StackRemove.bytesInWord width
    let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
    let labst := LabToTarget.makeInit (C := C) mc ffi t m
      (fun a => ((heapStackDm a || byteArena a) || bitmapsDm a) && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
    holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
    holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
    1024 * biw ≤ t.regs r2 - t.regs r1 ∧
    (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
    m (t.regs r1) = .word bitmapPtr ∧
    m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
      biw * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
    m (t.regs r1 + 4 * biw) =
      .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
    SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
      (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
      (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)) →
    labAssumptionsWithArena c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset bitmaps p labst
      (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp (fun _ => (ltc, [], [])) arena := by
  intro regNames r1 r2 biw heapStackDm sp maxHeap labst hpi
  have good : goodDimindex width := hmc.1
  obtain ⟨hl, hpc, hio, hcc, hmd, hsmd, hgc, hgco, hsp, hsave, n4, n3, n2, n1, n0, hbij,
    hnf⟩ := panToTargetLabstFacts (C := C) c mc ffi t m
      (fun w => (heapStackDm w || byteArena w) || bitmapsDm w) sdm ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
      panCode col wprog bitmaps c'' fs p hcfg hmc hinit hisa hwtw hwts hnodup
  have hma := memoryAssumptionFromMachineWithArena (C := C) good regNames mc ffi t m bitmapPtr bitmapsDm
    (fun a => sdm a && holByteAligned a) ms
    (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p) comp
    bytes cbspace
    (fun _ => (ltc, StackToLab.compileNoStubs regNames c.stackConf.jump
      mc.target.config.addrOffset sp []))
    bitmaps dataSp byteArena arena wordArenaEq arenaHeap arenaBitmap hpi
  exact ⟨good, rfl, rfl, hnf, hma, hcfg.2.2.2.2.2.2.2.2.2.1, hl, hpc, hio, hcc, hmd, hsmd,
    hgc, fun _ => hgco, hsp, hsave, n4, n3, n2, n1, n0, hbij⟩

#print axioms fullMakeInitAssumptionsWithArena
end InitE.Op5
