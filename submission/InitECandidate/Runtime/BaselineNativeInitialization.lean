import InitECandidate.Runtime.PipelineNativeInitialization
import InitECandidate.Runtime.BaselineCompilerResult
import InitECandidate.Proofs.PanInstallation
import InitE.SourceCodeFacts
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime.LabToTarget
open InitE
open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget
open InitECandidate.Proofs
open Flapjack.Compiler.Backend.RiscVConfig

/-- Native initialization guards for the actual baseline artifact and installed machine.
Every compiler, source, memory and MMIO premise is discharged internally. -/
theorem baseline_native_initialization (input : Guest.InputBlob) :
    ∃ (col : List (Option (Spt Nat)))
      (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
      (wconf : WordToStack.Native.Config) (fs : List Nat)
      (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
      WordToWord.compile baselineCompilerConfig.wordToWordConf baselineMachineConfig.target.config
        (panToWordCompileProgHOL baselineMachineConfig.target.config.isa sourceDeclarations) = (col, wprog) ∧
      WordToStack.Native.compileNative baselineMachineConfig.target.config false wprog = (InitECandidate.bitmaps, wconf, fs, p) ∧
      LabToTarget.compile baselineMachineConfig.target.config baselineCompilerConfig.labConf
        (StackToLab.compile baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf (2 * DataToWord.maxHeapLimit 64 baselineCompilerConfig.dataConf - 1)
          (baselineMachineConfig.target.config.regCount - (baselineMachineConfig.target.config.avoidRegs.length + 3))
          baselineMachineConfig.target.config.addrOffset p) = some (InitECandidate.nativeCode, ltconf) ∧
    ∃ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapsDm sdm : BitVec 64 → Bool),
      (∀ a, (sourceInitialState input).memaddrs a → m a = (wlabWlocExact ∘ (sourceInitialState input).memory) a) ∧
      (sourceInitialState input).shMemaddrs = (fun a => sdm a = true ∧ holByteAligned a = true) ∧
      (let regNames := baselineCompilerConfig.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec 64 → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := baselineMachineConfig.target.config.regCount - (baselineMachineConfig.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit 64 baselineCompilerConfig.dataConf - 1
    ∃ i, CompilationInstallationPremises baselineMachineConfig (sourceFfi input) baselineInstalledState
      (StackToLab.compile baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf maxHeap sp baselineMachineConfig.target.config.addrOffset p)
      baselineMachineConfig.target.config baselineCompilerConfig.labConf ltconf InitECandidate.nativeCode 620 i t m
      (fun w => heapStackDm w || bitmapsDm w) sdm
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames baselineCompilerConfig.stackConf.jump
        baselineMachineConfig.target.config.addrOffset sp []))) := by
  obtain ⟨depth, compiled⟩ := baseline_compiler_result
  exact compiled_installed_initialization baselineCompilerConfig baselineMachineConfig
    (sourceFfi input) baselineInstalledState InitECandidate.nativeCode 620 sourceDeclarations
    InitECandidate.bitmaps baselineConfig
    depth
    (oracleBackendConfigOk WordBackend.oracles)
    (riscvMachineConfigOk baselineMachineConfig baseline_machine_isRiscv) (by decide)
    compiled sourceDistinctFunctions (by change True; trivial)
    0 (wlabWlocExact ∘ (sourceInitialState input).memory)
    (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs
    (baseline_pan_installed input) sourceGoodCode

#print axioms baseline_native_initialization
end InitECandidate.Runtime.LabToTarget
