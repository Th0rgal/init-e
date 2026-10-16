import InitECandidate.Runtime.PipelineNativeInitialization
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMachineToLab
import Flapjack.Pancake.Proofs.PanToTarget.PanInstalled
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.RiscV.Target

/-- A single installed memory witness supplies both native and stack entry premises. -/
theorem installed_pipeline_joint_initialization {σ : Type}
    (c : Backend.Config) (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState σ)
    (ms : riscv_state) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (DeclHOL 64)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (bitmaps : List (BitVec 64))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg 64))
    (ltconf : LabToTarget.Config)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc)
    (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hlab : LabToTarget.compile mc.target.config c.labConf
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) = some (bytes, ltconf))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hffiOk : match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s)
    -- `pan_installed`'s components
    (dataSp : Nat) (pMem : BitVec 64 → WordLocW 64)
    (pDom sharedDom : BitVec 64 → Prop)
    (installed : panInstalled bytes cbspace bitmaps dataSp ltconf.ffiNames
      (BackendProof.heapRegs c.stackConf.regNames) mc ltconf.shmemExtra ms pMem pDom sharedDom)
    (hsource : pancakeGoodCodeHOL panCode = true) :
    ∃ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapsDm sdm : BitVec 64 → Bool),
      (∀ a, pDom a → m a = pMem a) ∧
      sharedDom = (fun a => sdm a = true ∧ holByteAligned a = true) ∧
      (let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec 64 → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit 64 c.dataConf - 1
    let labst := LabToTarget.makeInit mc ffi t m
      (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      (LabToTarget.compile mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
    (∃ i, CompilationInstallationPremises mc ffi ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      mc.target.config c.labConf ltconf bytes cbspace i t m
      (fun w => heapStackDm w || bitmapsDm w) sdm
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))) ∧
    StackToLab.Proofs.FullMakeInitSemantics.Assumptions c.stackConf c.dataConf maxHeap sp
      mc.target.config.addrOffset bitmaps p labst
      (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp (fun _ => (ltconf, [], []))) := by
  obtain ⟨t, m, bitmapPtr, bitmapsDm, sdm, agreement, init, shared,
    align1, align2, alignBitmap, order, size, disjoint, header0, header1, header2,
    header3, header4, bitmapMemory, names, mmio⟩ := installed
  refine ⟨t, m, bitmapsDm, sdm, agreement, shared, ?_, ?_⟩
  · exact pipeline_initialization_from_source c mc ffi t m bitmapsDm sdm ms bytes cbspace
      panCode col wprog bitmaps wconf fs p ltconf hcfg hmc hisa hwtw hwts hlab hnodup hffiOk
      init names mmio hsource
  · exact panToTargetFullMakeInitAssumptions c mc ffi t m bitmapPtr bitmapsDm sdm ms
      (LabToTarget.compile mc.target.config) bytes cbspace ltconf panCode col wprog bitmaps
      wconf fs p dataSp hcfg hmc hinit hisa hwtw hwts hnodup
      ⟨align1, align2, alignBitmap, order, size, disjoint, header0, header1, header2,
        header3, header4, bitmapMemory⟩

/-- The full compiler result supplies the intermediate stages for the joint state. -/
theorem compiled_installed_joint_initialization {σ : Type}
    (c : Backend.Config) (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState σ)
    (ms : riscv_state) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (DeclHOL 64))
    (bitmaps : List (BitVec 64)) (finalConfig : Backend.Config) (stackMax : Option Nat)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc)
    (hisa : mc.target.config.isa ≠ .ag32)
    (compiled : compileProgMax c mc panCode = (some (bytes, bitmaps, finalConfig), stackMax))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hffiOk : match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s)
    -- `pan_installed`'s components
    (dataSp : Nat) (pMem : BitVec 64 → WordLocW 64)
    (pDom sharedDom : BitVec 64 → Prop)
    (installed : panInstalled bytes cbspace bitmaps dataSp finalConfig.labConf.ffiNames
      (BackendProof.heapRegs c.stackConf.regNames) mc finalConfig.labConf.shmemExtra ms pMem pDom sharedDom)
    (hsource : pancakeGoodCodeHOL panCode = true) :
    ∃ (col : List (Option (Spt Nat)))
      (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
      (wconf : WordToStack.Native.Config) (fs : List Nat)
      (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
      WordToWord.compile c.wordToWordConf mc.target.config
        (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog) ∧
      WordToStack.Native.compileNative mc.target.config false wprog = (bitmaps, wconf, fs, p) ∧
      LabToTarget.compile mc.target.config c.labConf
        (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
          (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
          mc.target.config.addrOffset p) = some (bytes, ltconf) ∧
    ∃ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapsDm sdm : BitVec 64 → Bool),
      (∀ a, pDom a → m a = pMem a) ∧
      sharedDom = (fun a => sdm a = true ∧ holByteAligned a = true) ∧
      (let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec 64 → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit 64 c.dataConf - 1
    let labst := LabToTarget.makeInit mc ffi t m
      (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      (LabToTarget.compile mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat 64 bytes.length) cbspace
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
    (∃ i, CompilationInstallationPremises mc ffi ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      mc.target.config c.labConf ltconf bytes cbspace i t m
      (fun w => heapStackDm w || bitmapsDm w) sdm
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))) ∧
    StackToLab.Proofs.FullMakeInitSemantics.Assumptions c.stackConf c.dataConf maxHeap sp
      mc.target.config.addrOffset bitmaps p labst
      (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp (fun _ => (ltconf, [], []))) := by
  obtain ⟨col, wprog, wconf, fs, p, ltconf, wordCompiled, stackCompiled, labCompiled,
    finalEq, depth⟩ := compileProgMax_some c mc panCode bytes bitmaps finalConfig stackMax compiled
  rw [finalEq] at installed
  exact ⟨col, wprog, wconf, fs, p, ltconf, wordCompiled, stackCompiled, labCompiled,
    installed_pipeline_joint_initialization c mc ffi ms bytes cbspace panCode col wprog bitmaps
      wconf fs p ltconf hcfg hmc hinit hisa wordCompiled stackCompiled labCompiled hnodup hffiOk
      dataSp pMem pDom sharedDom installed hsource⟩

#print axioms compiled_installed_joint_initialization

#print axioms installed_pipeline_joint_initialization
end InitECandidate.Runtime.LabToTarget
