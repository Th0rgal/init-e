import InitECandidate.Runtime.EndpointLoopEntry
import InitECandidate.Runtime.EndpointFrontendNativeAffine
import InitECandidate.Runtime.EndpointNativeOutcomesAffine
import InitECandidate.Runtime.BaselineLoopNative
import InitECandidate.Runtime.BaselineLoopEntry
import InitECandidate.Runtime.BaselineAffineFuelMono
import InitECandidate.Runtime.CrepAffine
import InitECandidate.Runtime.CrepEntryAffine
import InitECandidate.Runtime.CrepWholeEntryAffine
import InitECandidate.Runtime.BaselineCrepLoopEntryAffine
import InitECandidate.Runtime.BaselineFrontendNativeAffine
import InitECandidate.Runtime.BaselineNativeOutcomesAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

theorem endpoint_loop_return_native_affine {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (base capacity : BitVec 64)
    (related : loopToWordStateRelHOLExact (endpointLoopState entry base capacity) (endpointFrontendState entry))
    (fuel : Nat)
    (post : LoopSemStateFiniteExact 64 Guest.HostMemory)
    (values : List (WordLocW 64))
    (run : LoopSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [] none : HolLoopProg 64)
      {endpointLoopState entry base capacity with clock := fuel} = (some (.result values),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordPost,wordRun,ffi⟩ := LoopToWord.entry_return_same_clock
    (endpointLoopState entry base capacity) (endpointFrontendState entry) BvlToBvi.initGlobalsLocation
    fuel values post related rfl (by
      change sptLookup 0 (sptInsert 0 (.loc 1 0 : WordLocW 64) .ln) = _
      rw [sptLookup_sptInsert_same]) (Or.inr rfl) run
  obtain ⟨final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_frontend_return_native_affine entry fuel wordPost values wordRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

theorem endpoint_loop_ffi_native_affine {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (base capacity : BitVec 64)
    (related : loopToWordStateRelHOLExact (endpointLoopState entry base capacity) (endpointFrontendState entry))
    (fuel : Nat)
    (post : LoopSemStateFiniteExact 64 Guest.HostMemory)
    (event : HolFinalEvent)
    (run : LoopSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [] none : HolLoopProg 64)
      {endpointLoopState entry base capacity with clock := fuel} = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordPost,wordRun,ffi⟩ := LoopToWord.entry_ffi_same_clock
    (endpointLoopState entry base capacity) (endpointFrontendState entry) BvlToBvi.initGlobalsLocation
    fuel event post related rfl (by
      change sptLookup 0 (sptInsert 0 (.loc 1 0 : WordLocW 64) .ln) = _
      rw [sptLookup_sptInsert_same]) (Or.inr rfl) run
  obtain ⟨final,outcome,count,native,bound,nativeRun,observation⟩ :=
    endpoint_frontend_ffi_native_affine entry fuel wordPost event wordRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms endpoint_loop_return_native_affine
#print axioms endpoint_loop_ffi_native_affine
end InitECandidate.Runtime
