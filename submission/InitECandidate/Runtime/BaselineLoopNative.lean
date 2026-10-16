import InitECandidate.Runtime.BaselineLoopEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

theorem baseline_loop_return_native {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (base capacity : BitVec 64)
    (related : loopToWordStateRelHOLExact (entryLoopState entry base capacity) (entryFrontendState entry))
    (fuel : Nat)
    (post : LoopSemStateFiniteExact 64 Guest.HostMemory)
    (values : List (WordLocW 64))
    (run : LoopSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [] none : HolLoopProg 64)
      {entryLoopState entry base capacity with clock := fuel} = (some (.result values),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordPost,wordRun,ffi⟩ := LoopToWord.entry_return_same_clock
    (entryLoopState entry base capacity) (entryFrontendState entry) BvlToBvi.initGlobalsLocation
    fuel values post related rfl (by
      change sptLookup 0 (sptInsert 0 (.loc 1 0 : WordLocW 64) .ln) = _
      rw [sptLookup_sptInsert_same]) (Or.inr rfl) run
  obtain ⟨final,outcome,count,native,bound,nativeRun,observation⟩ :=
    baseline_frontend_return_native entry fuel wordPost values wordRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

theorem baseline_loop_ffi_native {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (base capacity : BitVec 64)
    (related : loopToWordStateRelHOLExact (entryLoopState entry base capacity) (entryFrontendState entry))
    (fuel : Nat)
    (post : LoopSemStateFiniteExact 64 Guest.HostMemory)
    (event : HolFinalEvent)
    (run : LoopSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [] none : HolLoopProg 64)
      {entryLoopState entry base capacity with clock := fuel} = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordPost,wordRun,ffi⟩ := LoopToWord.entry_ffi_same_clock
    (entryLoopState entry base capacity) (entryFrontendState entry) BvlToBvi.initGlobalsLocation
    fuel event post related rfl (by
      change sptLookup 0 (sptInsert 0 (.loc 1 0 : WordLocW 64) .ln) = _
      rw [sptLookup_sptInsert_same]) (Or.inr rfl) run
  obtain ⟨final,outcome,count,native,bound,nativeRun,observation⟩ :=
    baseline_frontend_ffi_native entry fuel wordPost event wordRun
  rw [ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms baseline_loop_return_native
#print axioms baseline_loop_ffi_native
end InitECandidate.Runtime
