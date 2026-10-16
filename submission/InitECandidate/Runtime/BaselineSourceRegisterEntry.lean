import InitECandidate.Runtime.BaselineWordMemoryEntry
import InitECandidate.Runtime.BaselineInstalledRegisters
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

def EntrySourceRegisters {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) : Prop :=
  entry.asm.regs 11 = BitVec.ofNat 64 sourceBase ∧
  entry.asm.regs 12 = BitVec.ofNat 64 stackStart ∧
  entry.asm.regs 13 = BitVec.ofNat 64 ramEnd

/-- Concrete runtime initialization retains the machine installation's fixed
incoming pointers together with word-only heap memory and all native guarantees. -/
theorem baselineRuntimeEntry_source_registers_exists (input : Guest.InputBlob) :
    ∃ entry : BaselineRuntimeEntry input, EntryHeapWords entry ∧ EntrySourceRegisters entry := by
  obtain ⟨cfg,asm,memory,bitmapDomain,sharedDomain,i,words,agreement,shared,guards,assumptions⟩ :=
    LabToTarget.WordMemory.baseline_word_actual_joint_initialization input
  obtain ⟨source,selected,wordInit⟩ := WordToStack.selected_word_initialization riscvConfig
    baselineCompilerConfig.wordToWordConf sourceDeclarations [] BackendStages.Native.programs0
    InitECandidate.bitmaps BackendStages.Native.wordConfig (0 :: BackendStages.Native.frames0)
    BackendStages.Native.stack cfg baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf
    entryHeapLimit entrySp riscvConfig.addrOffset
    (LabToTarget.baselineLabState input cfg asm memory bitmapDomain sharedDomain) entrySaveRegs 0
    (Or.inr rfl) (by decide) (by decide) LabToTarget.baseline_word_program
    BackendStages.Native.native_submitted_bitmaps_eq assumptions
  have nativeBound : ∀ fuel post outcome,
      LabSem.evaluate {LabToTarget.baselineLabState input cfg asm memory bitmapDomain sharedDomain with clock := fuel} =
        (.halt outcome,post) → ∃ count native, count ≤ 14467153 * fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState = (.halt outcome,native,post.ffi) := by
    intro fuel post outcome run
    obtain ⟨count,native,bound,nativeRun⟩ := LabToTarget.actual_aligned_compiled_native_bound
      baselineMachineConfig (sourceFfi input) baselineInstalledState riscvConfig
      baselineCompilerConfig.labConf cfg InitECandidate.nativeCode 620 i asm memory _ sharedDomain _
      guards fuel post outcome rfl run
    exact ⟨count,native,by simpa only [LiteralFacts.nativeCode_length] using bound,nativeRun⟩
  let entry : BaselineRuntimeEntry input :=
    ⟨cfg,asm,memory,bitmapDomain,sharedDomain,source,agreement,shared,assumptions,selected,wordInit,nativeBound⟩
  refine ⟨entry,?_,?_⟩
  · exact StackRemove.selected_words_of_full_initialization baselineCompilerConfig.stackConf
      baselineCompilerConfig.dataConf entryHeapLimit entrySp riscvConfig.addrOffset InitECandidate.bitmaps
      BackendStages.Native.stack (LabToTarget.baselineLabState input cfg asm memory bitmapDomain sharedDomain)
      entrySaveRegs 0 (entryStackOracle cfg) assumptions words source selected
  · exact baseline_good_init_registers asm memory _ sharedDomain guards.2.2.2.2.2.2.2.2.1

#print axioms baselineRuntimeEntry_source_registers_exists
end InitECandidate.Runtime
