import InitECandidate.Runtime.CompiledNativeBudget
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMachineToLab
import Flapjack.Pancake.Proofs.PanToTarget.PanInstalled
namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.RiscV.Target

/-- The actual Pancake backend pipeline discharges compiler-oracle and no-install
premises; installation metadata supplies the remaining native entry guards. -/
theorem pipeline_initialization_of_goodCode {σ : Type}
    (c : Backend.Config) (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState σ)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool) (ms : riscv_state) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (DeclHOL 64)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (bitmaps : List (BitVec 64))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg 64))
    (ltconf : LabToTarget.Config)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
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
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hffi : ltconf.ffiNames = some mc.ffiNames)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff),
            rec.reg, BitVec.ofNat 64 rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + ffiOffset * (i + 3) < 2 ^ 64)
    -- stage A2's conclusion
    (hgc : LabToTarget.goodCode mc.target.config (.ln : Spt (Spt Nat))
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit 64 c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p)) :
    let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec 64 → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit 64 c.dataConf - 1
    ∃ i, CompilationInstallationPremises mc ffi ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      mc.target.config c.labConf ltconf bytes cbspace i t m
      (fun w => heapStackDm w || bitmapsDm w) sdm
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp [])) := by
  intro regNames r1 r2 heapStackDm sp maxHeap
  have hpos : c.labConf.pos = 0 := hcfg.2.2.2.2.1
  have hlabels : c.labConf.labels = .ln := hcfg.2.2.2.2.2.1
  obtain ⟨ffis, hffis, i, hi⟩ := BackendProof.compileLabIMPMmioPcsMinIndex mc.target.config
    c.labConf _ bytes ltconf ⟨hlab, hffiOk⟩
  rw [hffi] at hffis
  cases hffis
  obtain ⟨hshm, hmmioI, hbound⟩ := hmmio i hi
  have horacle := panToTargetCompilerOracleOk mc.target.config c.labConf ltconf _ bytes
    mc.ffiNames regNames c.stackConf.jump mc.target.config.addrOffset sp hlab hpos hffi
  have hnis := panToTargetNoInstallOrNoShareMem panCode mc.target.config mc.target.config.isa _
    c.wordToWordConf col wprog bitmaps wconf fs p c.stackConf c.dataConf maxHeap sp
    mc.target.config.addrOffset mc.ffiNames ⟨hnodup, hisa, rfl, hwtw, hwts⟩
  exact ⟨i, hmc, fun _ => horacle, hgc, rfl, hlabels, hpos, hlab, hffi, hgi,
    hshm, hmmioI, hnis, hi, hbound, fun ffis h => by rw [h] at hffiOk; exact hffiOk⟩

/-- Source good-code checks derive the label good-code guard internally. -/
theorem pipeline_initialization_from_source {σ : Type}
    (c : Backend.Config) (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState σ)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool) (ms : riscv_state) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (DeclHOL 64)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (bitmaps : List (BitVec 64))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg 64))
    (ltconf : LabToTarget.Config)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
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
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hffi : ltconf.ffiNames = some mc.ffiNames)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff),
            rec.reg, BitVec.ofNat 64 rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + ffiOffset * (i + 3) < 2 ^ 64)
    -- stage A2's conclusion
    (hsource : pancakeGoodCodeHOL panCode = true) :
    let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec 64 → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit 64 c.dataConf - 1
    ∃ i, CompilationInstallationPremises mc ffi ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      mc.target.config c.labConf ltconf bytes cbspace i t m
      (fun w => heapStackDm w || bitmapsDm w) sdm
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp [])) := by
  exact pipeline_initialization_of_goodCode c mc ffi t m bitmapsDm sdm ms bytes cbspace
    panCode col wprog bitmaps wconf fs p ltconf hcfg hmc hisa hwtw hwts hlab hnodup hffiOk
    hgi hffi hmmio
    (panToTargetGoodCodeFromSource (β := Nat) c mc panCode col wprog bitmaps wconf fs p
      hcfg hmc.1 hisa hwtw hwts hnodup hsource)

/-- Installation supplies all memory/MMIO guards while retaining source memory agreement. -/
theorem installed_pipeline_initialization {σ : Type}
    (c : Backend.Config) (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState σ)
    (ms : riscv_state) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (DeclHOL 64)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (bitmaps : List (BitVec 64))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg 64))
    (ltconf : LabToTarget.Config)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
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
    ∃ i, CompilationInstallationPremises mc ffi ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      mc.target.config c.labConf ltconf bytes cbspace i t m
      (fun w => heapStackDm w || bitmapsDm w) sdm
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))) := by
  obtain ⟨t, m, bitmapPtr, bitmapsDm, sdm, agreement, init, shared,
    align1, align2, alignBitmap, order, size, disjoint, header0, header1, header2,
    header3, header4, bitmapMemory, names, mmio⟩ := installed
  refine ⟨t, m, bitmapsDm, sdm, agreement, shared, ?_⟩
  exact pipeline_initialization_from_source c mc ffi t m bitmapsDm sdm ms bytes cbspace
    panCode col wprog bitmaps wconf fs p ltconf hcfg hmc hisa hwtw hwts hlab hnodup hffiOk
    init names mmio hsource

/-- The completed compiler artifact supplies every intermediate pass result. -/
theorem compiled_installed_initialization {σ : Type}
    (c : Backend.Config) (mc : MachineConfig 64 riscv_state RiscVProjection) (ffi : HolFfiState σ)
    (ms : riscv_state) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (DeclHOL 64))
    (bitmaps : List (BitVec 64)) (finalConfig : Backend.Config) (stackMax : Option Nat)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
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
    ∃ i, CompilationInstallationPremises mc ffi ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      mc.target.config c.labConf ltconf bytes cbspace i t m
      (fun w => heapStackDm w || bitmapsDm w) sdm
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))) := by
  obtain ⟨col, wprog, wconf, fs, p, ltconf, wordCompiled, stackCompiled, labCompiled,
    finalEq, depth⟩ := compileProgMax_some c mc panCode bytes bitmaps finalConfig stackMax compiled
  rw [finalEq] at installed
  exact ⟨col, wprog, wconf, fs, p, ltconf, wordCompiled, stackCompiled, labCompiled,
    installed_pipeline_initialization c mc ffi ms bytes cbspace panCode col wprog bitmaps
      wconf fs p ltconf hcfg hmc hisa wordCompiled stackCompiled labCompiled hnodup hffiOk
      dataSp pMem pDom sharedDom installed hsource⟩

#print axioms compiled_installed_initialization

#print axioms installed_pipeline_initialization

#print axioms pipeline_initialization_from_source

#print axioms pipeline_initialization_of_goodCode
end InitECandidate.Runtime.LabToTarget
