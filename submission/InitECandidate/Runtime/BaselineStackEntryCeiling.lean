import InitECandidate.Runtime.StackEntryWorkCeiling
import InitECandidate.Runtime.BaselineWordNativeBudget
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Fixed natural-valued ceiling for every procedure in the actual named code. -/
noncomputable def baselineNamedLimit : Nat := StackToLab.codeSizeLimit BackendStages.Named.stack

noncomputable def entryNamedState {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (fuel : Nat) := s3 baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
      entryHeapLimit entrySp riscvConfig.addrOffset BackendStages.Native.stack
      {entry.lab with clock := fuel} entrySaveRegs (entryStackOracle entry.cfg)

theorem entryNamedState_code {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    (entryNamedState entry fuel).code = sptFromAList BackendStages.Named.stack := by
  have removed : code2 baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
      entryHeapLimit entrySp riscvConfig.addrOffset BackendStages.Native.stack = BackendStages.Removed.stack := by
    unfold code2 code1
    rw [BackendStages.Raw.compile_eq]
    change StackRemove.compileHOL false riscvConfig.addrOffset
      (StackToLab.isGenGc RiscVConfig.pancakeRiscVBackendConfig.dataConf.gcKind)
      (2 * DataToWord.maxHeapLimit 64 RiscVConfig.pancakeRiscVBackendConfig.dataConf - 1)
      (riscvConfig.regCount - (riscvConfig.avoidRegs.length + 3)) BvlToBvi.initGlobalsLocation
      (StackAlloc.compile RiscVConfig.pancakeRiscVBackendConfig.dataConf BackendStages.Raw.stack) = _
    rw [BackendStages.Alloc.compile_eq]
    exact BackendStages.Removed.compile_eq
  change sptFromAList (StackNames.compileHOL baselineCompilerConfig.stackConf.regNames
    (code2 baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf entryHeapLimit entrySp
      riscvConfig.addrOffset BackendStages.Native.stack)) = _
  rw [removed]
  exact congrArg sptFromAList BackendStages.Named.compile_eq

theorem entryNamedState_bounded {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    StackToLab.CodeSizeState baselineNamedLimit (entryNamedState entry fuel) := by
  apply StackToLab.CodeSizeState.of_lists baselineNamedLimit _ BackendStages.Named.stack
    (entryNamedState_code entry fuel) (Nat.le_refl _)
  intro n
  change 0 ≤ baselineNamedLimit
  exact Nat.zero_le _

/-- The actual entry budget has a ceiling depending only on its initial clock
and the fixed named code, with no runtime work assumption. -/
theorem baseline_entryWork_ceiling {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input)
    (fuel : Nat) : StackToLab.entryWork 0 (entryNamedState entry fuel) ≤
      2 * workCeiling baselineNamedLimit fuel baselineNamedLimit :=
  StackToLab.entryWork_ceiling baselineNamedLimit 0 _ (entryNamedState_bounded entry fuel)

#print axioms entryNamedState_code
#print axioms entryNamedState_bounded
#print axioms baseline_entryWork_ceiling
end InitECandidate.Runtime
