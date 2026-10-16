import InitECandidate.Runtime.BaselineActualNativeInitialization
import InitECandidate.Runtime.ActualUnfilteredNativeBudget
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime.LabToTarget
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target

/-- The concrete post-installation label initializer, including both aligned domains. -/
noncomputable def baselineLabState (input : Guest.InputBlob) (ltconf : LabToTarget.Config)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool) : State 64 Config Guest.HostMemory :=
  makeInit baselineMachineConfig (sourceFfi input) t m
    (fun a => (decide
      (t.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 2) ≤ a ∧
       a < t.regs (StackNames.findNameSpt baselineCompilerConfig.stackConf.regNames 4)) ||
      bitmapsDm a) && holByteAligned a)
    (fun a => sdm a && holByteAligned a) baselineInstalledState BackendStages.Sections.program
    (compile riscvConfig)
    (baselineMachineConfig.target.getPc baselineInstalledState +
      BitVec.ofNat 64 InitECandidate.nativeCode.length) 620
    (fun _ => (ltconf, StackToLab.compileNoStubs baselineCompilerConfig.stackConf.regNames
      baselineCompilerConfig.stackConf.jump riscvConfig.addrOffset
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) []))

/-- The baseline's actual installed code has a linear native runtime bound for
every terminating label execution. All static and installation guards are proved. -/
theorem baseline_lab_native_bound (input : Guest.InputBlob) :
    ∃ (ltconf : LabToTarget.Config) (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
      (bitmapsDm sdm : BitVec 64 → Bool),
      (∀ a, (sourceInitialState input).memaddrs a →
        m a = (wlabWlocExact ∘ (sourceInitialState input).memory) a) ∧
      (sourceInitialState input).shMemaddrs =
        (fun a => sdm a = true ∧ holByteAligned a = true) ∧
      ∀ fuel post outcome,
        evaluate {baselineLabState input ltconf t m bitmapsDm sdm with clock := fuel} =
          (.halt outcome, post) →
        ∃ count native, count ≤ 14467153 * fuel ∧
          evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
            (.halt outcome, native, post.ffi) := by
  obtain ⟨ltconf, t, m, bitmapsDm, sdm, i, agreement, shared, guards⟩ :=
    baseline_actual_native_initialization input
  refine ⟨ltconf, t, m, bitmapsDm, sdm, agreement, shared, ?_⟩
  intro fuel post outcome run
  obtain ⟨count, native, bound, nativeRun⟩ := actual_aligned_compiled_native_bound baselineMachineConfig (sourceFfi input)
    baselineInstalledState riscvConfig baselineCompilerConfig.labConf ltconf
    InitECandidate.nativeCode 620 i t m _ sdm _ guards fuel post outcome rfl run
  exact ⟨count, native, by simpa only [LiteralFacts.nativeCode_length] using bound, nativeRun⟩

#print axioms baseline_lab_native_bound
end InitECandidate.Runtime.LabToTarget
