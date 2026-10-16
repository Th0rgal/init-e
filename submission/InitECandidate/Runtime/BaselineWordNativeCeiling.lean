import InitECandidate.Runtime.BaselineRemovalCeiling
import InitECandidate.Runtime.BaselineWordNativeAffine
import InitECandidate.Runtime.InitializedWordToLabAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

theorem baseline_word_return_native_ceiling {input : Guest.InputBlob}
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
      removedClock ≤ rawClock + baselineBitmapScale * workCeiling baselineRemovalLimit rawClock
        (sizeOf (.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64)) + 1 ∧
      clocks ≤ (2 * baselineNamedLimit + 2) * removedClock + 4 * baselineNamedLimit ∧
      count ≤ 14467153 * (removedClock - 1 + clocks) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome, native, final.ffi) ∧
      ((outcome = .success ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordClock, rawClock, removedClock, clocks, final, outcome, count, native,
    wordBound, rawBound, removedBound, labelBound, nativeBound, evaluated, observation⟩ :=
    baseline_word_return_native_affine entry fuel wordPost values run
  have removal := baseline_removeWork_ceiling entry rawClock
  exact ⟨wordClock, rawClock, removedClock, clocks, final, outcome, count, native,
    wordBound, rawBound, by omega, labelBound, nativeBound, evaluated, observation⟩

#print axioms baseline_word_return_native_ceiling
end InitECandidate.Runtime
