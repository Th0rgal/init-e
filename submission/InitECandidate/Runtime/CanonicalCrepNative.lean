import InitECandidate.Runtime.BaselineWordMemoryEntry
import InitECandidate.Runtime.BaselineCrepNative
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

noncomputable def canonicalRuntimeEntry (input : Guest.InputBlob) : BaselineRuntimeEntry input :=
  Classical.choose (baselineRuntimeEntry_word_memory_exists input)

noncomputable def canonicalHeapBase (input : Guest.InputBlob) : BitVec 64 :=
  Classical.choose (entryLoopState_exists (canonicalRuntimeEntry input))

noncomputable def canonicalHeapCapacity (input : Guest.InputBlob) : BitVec 64 :=
  Classical.choose (Classical.choose_spec (entryLoopState_exists (canonicalRuntimeEntry input)))

theorem canonical_frontend_noLabels (input : Guest.InputBlob) :
    noLabelsHOL (entryFrontendState (canonicalRuntimeEntry input)).memory
      (fun address => (entryFrontendState (canonicalRuntimeEntry input)).mdomain address = true) :=
  entryFrontendState_noLabels _ (Classical.choose_spec (baselineRuntimeEntry_word_memory_exists input))

theorem canonical_loop_related (input : Guest.InputBlob) :
    loopToWordStateRelHOLExact
      (entryLoopState (canonicalRuntimeEntry input) (canonicalHeapBase input) (canonicalHeapCapacity input))
      (entryFrontendState (canonicalRuntimeEntry input)) :=
  Classical.choose_spec (Classical.choose_spec (entryLoopState_exists (canonicalRuntimeEntry input)))

noncomputable def canonicalCrepState (input : Guest.InputBlob) : CrepSemHOLState 64 Guest.HostMemory :=
  entryCrepState (canonicalRuntimeEntry input) (canonicalHeapBase input) (canonicalHeapCapacity input)

/-- Concrete entry-to-native transfer with initialization and memory guards
fully discharged; the source execution is the only dynamic premise. -/
theorem canonical_crep_return_native (input : Guest.InputBlob)
    (fuel : Nat) (post : CrepSemHOLState 64 Guest.HostMemory) (values : List (HolWordLab 64))
    (run : evalCrepSemHOLProgExact {canonicalCrepState input with clock := fuel}
      (.call none baselineCrepStart []) = (some (.return values),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + baselineCrepExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  exact baseline_crep_return_native (canonicalRuntimeEntry input) (canonicalHeapBase input)
    (canonicalHeapCapacity input) (canonical_loop_related input) (canonical_frontend_noLabels input)
    fuel post values run

#print axioms canonical_crep_return_native
/-- Concrete entry-to-native transfer with initialization and memory guards
fully discharged; the source execution is the only dynamic premise. -/
theorem canonical_crep_ffi_native (input : Guest.InputBlob)
    (fuel : Nat) (post : CrepSemHOLState 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : evalCrepSemHOLProgExact {canonicalCrepState input with clock := fuel}
      (.call none baselineCrepStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + baselineCrepExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  exact baseline_crep_ffi_native (canonicalRuntimeEntry input) (canonicalHeapBase input)
    (canonicalHeapCapacity input) (canonical_loop_related input) (canonical_frontend_noLabels input)
    fuel post event run

#print axioms canonical_crep_ffi_native
end InitECandidate.Runtime
