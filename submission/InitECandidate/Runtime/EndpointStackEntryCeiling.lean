import InitECandidate.Runtime.EndpointRuntimeEntry
import InitECandidate.Runtime.BaselineStackEntryCeiling
import InitECandidate.Runtime.StackEntryWorkCeiling
import InitECandidate.Runtime.BaselineWordNativeBudget
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

noncomputable def EndpointRuntimeEntry.lab {input : Guest.InputBlob} {endpoint : Flapjack.RiscV.L3.riscv_state} (entry : EndpointRuntimeEntry input endpoint) :=
  LabToTarget.endpointLabState input endpoint entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain

noncomputable def endpointNamedState {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (fuel : Nat) := s3 baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
      entryHeapLimit entrySp riscvConfig.addrOffset BackendStages.Native.stack
      {entry.lab with clock := fuel} entrySaveRegs (entryStackOracle entry.cfg)

theorem endpointNamedState_code {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat) :
    (endpointNamedState entry fuel).code = sptFromAList BackendStages.Named.stack := by
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

theorem endpointNamedState_bounded {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat) :
    StackToLab.CodeSizeState baselineNamedLimit (endpointNamedState entry fuel) := by
  apply StackToLab.CodeSizeState.of_lists baselineNamedLimit _ BackendStages.Named.stack
    (endpointNamedState_code entry fuel) (Nat.le_refl _)
  intro n
  change 0 ≤ baselineNamedLimit
  exact Nat.zero_le _

/-- The actual entry budget has a ceiling depending only on its initial clock
and the fixed named code, with no runtime work assumption. -/
theorem endpoint_entryWork_ceiling {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint)
    (fuel : Nat) : StackToLab.entryWork 0 (endpointNamedState entry fuel) ≤
      2 * workCeiling baselineNamedLimit fuel baselineNamedLimit :=
  StackToLab.entryWork_ceiling baselineNamedLimit 0 _ (endpointNamedState_bounded entry fuel)

#print axioms endpointNamedState_code
#print axioms endpointNamedState_bounded
#print axioms endpoint_entryWork_ceiling
end InitECandidate.Runtime
