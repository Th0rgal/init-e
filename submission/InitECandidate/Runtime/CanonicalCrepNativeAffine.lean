import InitECandidate.Runtime.CanonicalCrepNative
import InitECandidate.Runtime.BaselineSourceRegisterEntry
import InitECandidate.Runtime.BaselineCrepNativeAffine
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.CrepAffine
import InitECandidate.Runtime.CrepEntryAffine
import InitECandidate.Runtime.CrepWholeEntryAffine
import InitECandidate.Runtime.BaselineCrepLoopEntryAffine
import InitECandidate.Runtime.BaselineFrontendNativeAffine
import InitECandidate.Runtime.BaselineNativeOutcomesAffine
import InitECandidate.Runtime.BaselineLoopNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Concrete entry-to-native transfer with initialization and memory guards
fully discharged; the source execution is the only dynamic premise. -/
theorem canonical_crep_return_native_affine (input : Guest.InputBlob)
    (fuel : Nat) (post : CrepSemHOLState 64 Guest.HostMemory) (values : List (HolWordLab 64))
    (run : evalCrepSemHOLProgExact {canonicalCrepState input with clock := fuel}
      (.call none baselineCrepStart []) = (some (.return values),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + baselineCrepAffineExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  exact baseline_crep_return_native_affine (canonicalRuntimeEntry input) (canonicalHeapBase input)
    (canonicalHeapCapacity input) (canonical_loop_related input) (canonical_frontend_noLabels input)
    fuel post values run

#print axioms canonical_crep_return_native_affine
/-- Concrete entry-to-native transfer with initialization and memory guards
fully discharged; the source execution is the only dynamic premise. -/
theorem canonical_crep_ffi_native_affine (input : Guest.InputBlob)
    (fuel : Nat) (post : CrepSemHOLState 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : evalCrepSemHOLProgExact {canonicalCrepState input with clock := fuel}
      (.call none baselineCrepStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel (fuel + baselineCrepAffineExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  exact baseline_crep_ffi_native_affine (canonicalRuntimeEntry input) (canonicalHeapBase input)
    (canonicalHeapCapacity input) (canonical_loop_related input) (canonical_frontend_noLabels input)
    fuel post event run

#print axioms canonical_crep_ffi_native_affine
end InitECandidate.Runtime
