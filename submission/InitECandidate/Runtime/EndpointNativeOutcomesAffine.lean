import InitECandidate.Runtime.EndpointFrontendNative
import InitECandidate.Runtime.EndpointAffineNative
import InitECandidate.Runtime.BaselineNativeOutcomes
import InitECandidate.Runtime.BaselineFrontendNativeAffine
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.CrepAffine
import InitECandidate.Runtime.CrepEntryAffine
import InitECandidate.Runtime.CrepWholeEntryAffine
import InitECandidate.Runtime.BaselineCrepLoopEntryAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

theorem endpoint_frontend_ffi_native_affine {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat)
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (event : HolFinalEvent)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {endpointFrontendState entry with clock := fuel} = (some (.finalFfi event),post)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  obtain ⟨optimized, evaluated, ffi, _, stack, limit⟩ :=
    endpoint_frontend_optimized_run entry fuel _ post run (by simp)
  obtain ⟨final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_word_ffi_native_affine_bound entry fuel optimized event evaluated
  rw [ffi,stack,limit] at observation
  exact ⟨final,outcome,count,native,bound,nativeRun,observation⟩

theorem endpoint_frontend_resource_native_affine {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat)
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {endpointFrontendState entry with clock := fuel} = (some .notEnoughSpace,post)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ count native,
      count ≤ baselineNativeAffineFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt .resourceLimitHit,native,final.ffi) ∧
      (final.ffi = post.ffi ∨
        (List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  obtain ⟨optimized, evaluated, ffi, _, stack, limit⟩ :=
    endpoint_frontend_optimized_run entry fuel _ post run (by simp)
  obtain ⟨final,count,native,bound,nativeRun,observation⟩ :=
    endpoint_word_resource_native_affine_bound entry fuel optimized evaluated
  rw [ffi,stack,limit] at observation
  exact ⟨final,count,native,bound,nativeRun,observation⟩

#print axioms endpoint_frontend_ffi_native_affine
#print axioms endpoint_frontend_resource_native_affine
end InitECandidate.Runtime
