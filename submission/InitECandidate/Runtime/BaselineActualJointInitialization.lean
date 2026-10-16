import InitECandidate.Runtime.BaselineJointInitialization
import InitECandidate.Runtime.BaselineLabNativeBudget
import InitECandidate.Runtime.BaselinePipelineCode
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime.LabToTarget
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target

/-- One concrete witness supports both native execution and the earlier stack pipeline. -/
theorem baseline_actual_joint_initialization (input : Guest.InputBlob) :
    ∃ (ltconf : LabToTarget.Config) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapsDm sdm : BitVec 64 → Bool) (i : Nat),
      (∀ a, (sourceInitialState input).memaddrs a →
        m a = (wlabWlocExact ∘ (sourceInitialState input).memory) a) ∧
      (sourceInitialState input).shMemaddrs =
        (fun a => sdm a = true ∧ holByteAligned a = true) ∧
      CompilationInstallationPremises baselineMachineConfig (sourceFfi input) baselineInstalledState
        BackendStages.Sections.program riscvConfig baselineCompilerConfig.labConf ltconf
        InitECandidate.nativeCode 620 i t m
        (fun w => decide
          (t.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2) ≤ w ∧
           w < t.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 4)) || bitmapsDm w)
        sdm (fun _ => (ltconf, StackToLab.compileNoStubs baselineCompilerConfig.stackConf.regNames
          baselineCompilerConfig.stackConf.jump riscvConfig.addrOffset
          (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) [])) ∧
      StackToLab.Proofs.FullMakeInitSemantics.Assumptions baselineCompilerConfig.stackConf
        baselineCompilerConfig.dataConf
        (2 * DataToWord.maxHeapLimit 64 baselineCompilerConfig.dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
        InitECandidate.bitmaps BackendStages.Native.stack
        (baselineLabState input ltconf t m bitmapsDm sdm)
        (fun k => decide (k ∈ baselineMachineConfig.calleeSavedRegs)) 0
        (fun _ => (ltconf, [], [])) := by
  obtain ⟨col, word, wc, fs, stack, ltconf, wordRun, stackRun, labRun,
    t, m, bitmapsDm, sdm, agreement, shared, ⟨i, guards⟩, stackAssumptions⟩ := baseline_joint_initialization input
  have stackEq := baseline_stack_program col word InitECandidate.bitmaps wc fs stack wordRun stackRun
  subst stack
  refine ⟨ltconf, t, m, bitmapsDm, sdm, i, agreement, shared, ?_, ?_⟩
  · change CompilationInstallationPremises baselineMachineConfig (sourceFfi input) baselineInstalledState
      (StackToLab.compile baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
        (2 * DataToWord.maxHeapLimit 64 baselineCompilerConfig.dataConf - 1)
        (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) riscvConfig.addrOffset
        BackendStages.Native.stack) riscvConfig baselineCompilerConfig.labConf ltconf
      InitECandidate.nativeCode 620 i t m _ sdm _ at guards
    rw [baseline_sections_program] at guards
    exact guards
  · have configEq : baselineMachineConfig.target.config = riscvConfig := rfl
    rw [configEq, baseline_sections_program] at stackAssumptions
    exact stackAssumptions

#print axioms baseline_actual_joint_initialization
end InitECandidate.Runtime.LabToTarget
