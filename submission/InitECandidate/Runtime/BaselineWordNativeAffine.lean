import InitECandidate.Runtime.BaselineStackEntryCeiling
import InitECandidate.Runtime.InitializedWordToLabAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- A Word final-FFI execution transfers through every remaining compiler stage
into native execution with explicit source-work and clock ceilings. -/
theorem baseline_word_ffi_native_affine {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (event : HolFinalEvent)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some (.finalFfi event), wordPost)) :
    ∃ wordClock rawClock removedClock clocks,
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      wordClock ≤ fuel + WordToStack.wordWork (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        {entryWordState entry.cfg entry.source with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + StackRemove.removeWork (.call none (.inl BvlToBvi.initGlobalsLocation) none)
        {entry.source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * baselineNamedLimit + 2) * removedClock + 4 * baselineNamedLimit ∧
      count ≤ 14467153 * (removedClock - 1 + clocks) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome, native, final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordClock, rawClock, removedClock, clocks, final, outcome,
    wordBound, rawBound, removedBound, labelBound, evaluated, observation⟩ :=
    StackToLab.initialized_word_ffi_to_lab_affine baselineCompilerConfig.stackConf
      baselineCompilerConfig.dataConf entryHeapLimit entrySp riscvConfig.addrOffset
      InitECandidate.bitmaps BackendStages.Native.stack entry.lab entrySaveRegs 0
      (entryStackOracle entry.cfg) entry.source fuel entry.stackAssumptions entry.selection
      baselineRawCodeFree (by intro n; rfl) riscvConfig
      (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) BackendStages.Native.programs0
      (entryWordOracle entry.cfg) wordPost entry.wordInitialized event baselineNamedLimit (entryNamedState_bounded entry) run
  obtain ⟨count, native, bound, nativeRun⟩ :=
    entry.nativeBound (removedClock - 1 + clocks) final outcome evaluated
  exact ⟨wordClock, rawClock, removedClock, clocks, final, outcome, count, native,
    wordBound, rawBound, removedBound, labelBound, bound, nativeRun, observation⟩

/-- Normal Word entry return, including the original resource-limit alternative. -/
theorem baseline_word_return_native_affine {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (values : List (WordLocW 64))
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some (.result (.loc 1 0) values), wordPost)) :
    ∃ wordClock rawClock removedClock clocks,
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      wordClock ≤ fuel + WordToStack.wordWork (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        {entryWordState entry.cfg entry.source with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + StackRemove.removeWork (.call none (.inl BvlToBvi.initGlobalsLocation) none)
        {entry.source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * baselineNamedLimit + 2) * removedClock + 4 * baselineNamedLimit ∧
      count ≤ 14467153 * (removedClock - 1 + clocks) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome, native, final.ffi) ∧
      ((outcome = .success ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordClock, rawClock, removedClock, clocks, final, outcome,
    wordBound, rawBound, removedBound, labelBound, evaluated, observation⟩ :=
    StackToLab.initialized_word_return_to_lab_affine baselineCompilerConfig.stackConf
      baselineCompilerConfig.dataConf entryHeapLimit entrySp riscvConfig.addrOffset
      InitECandidate.bitmaps BackendStages.Native.stack entry.lab entrySaveRegs 0
      (entryStackOracle entry.cfg) entry.source fuel entry.stackAssumptions entry.selection
      baselineRawCodeFree (by intro n; rfl) riscvConfig
      (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) BackendStages.Native.programs0
      (entryWordOracle entry.cfg) wordPost entry.wordInitialized values baselineNamedLimit (entryNamedState_bounded entry) run
  obtain ⟨count, native, bound, nativeRun⟩ :=
    entry.nativeBound (removedClock - 1 + clocks) final outcome evaluated
  exact ⟨wordClock, rawClock, removedClock, clocks, final, outcome, count, native,
    wordBound, rawBound, removedBound, labelBound, bound, nativeRun, observation⟩

/-- Source resource rejection remains native resource rejection. -/
theorem baseline_word_resource_native_affine {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some .notEnoughSpace, wordPost)) :
    ∃ wordClock rawClock removedClock clocks,
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ count native,
      wordClock ≤ fuel + WordToStack.wordWork (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        {entryWordState entry.cfg entry.source with clock := fuel} ∧
      rawClock ≤ 2 * wordClock ∧
      removedClock ≤ rawClock + StackRemove.removeWork (.call none (.inl BvlToBvi.initGlobalsLocation) none)
        {entry.source with clock := rawClock} + 1 ∧
      clocks ≤ (2 * baselineNamedLimit + 2) * removedClock + 4 * baselineNamedLimit ∧
      count ≤ 14467153 * (removedClock - 1 + clocks) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt .resourceLimitHit, native, final.ffi) ∧
      (final.ffi = wordPost.ffi ∨
        (List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordClock, rawClock, removedClock, clocks, final,
    wordBound, rawBound, removedBound, labelBound, evaluated, observation⟩ :=
    StackToLab.initialized_word_resource_to_lab_affine baselineCompilerConfig.stackConf
      baselineCompilerConfig.dataConf entryHeapLimit entrySp riscvConfig.addrOffset
      InitECandidate.bitmaps BackendStages.Native.stack entry.lab entrySaveRegs 0
      (entryStackOracle entry.cfg) entry.source fuel entry.stackAssumptions entry.selection
      baselineRawCodeFree (by intro n; rfl) riscvConfig
      (riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length)) BackendStages.Native.programs0
      (entryWordOracle entry.cfg) wordPost entry.wordInitialized baselineNamedLimit (entryNamedState_bounded entry) run
  obtain ⟨count, native, bound, nativeRun⟩ :=
    entry.nativeBound (removedClock - 1 + clocks) final .resourceLimitHit evaluated
  exact ⟨wordClock, rawClock, removedClock, clocks, final, count, native,
    wordBound, rawBound, removedBound, labelBound, bound, nativeRun, observation⟩

#print axioms baseline_word_return_native_affine
#print axioms baseline_word_resource_native_affine

#print axioms baseline_word_ffi_native_affine
end InitECandidate.Runtime
