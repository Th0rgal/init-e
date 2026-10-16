import InitECandidate.Runtime.BaselineCrepLoopEntry
import InitECandidate.Runtime.BaselineLoopNative
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Actual Crep entry execution composes through the checked compiler pipeline
into a uniform native-step ceiling, retaining the original resource alternative. -/
theorem baseline_crep_return_native {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (base capacity : BitVec 64)
    (related : loopToWordStateRelHOLExact (entryLoopState entry base capacity) (entryFrontendState entry))
    (words : noLabelsHOL (entryFrontendState entry).memory
      (fun address => (entryFrontendState entry).mdomain address = true))
    (fuel : Nat) (post : CrepSemHOLState 64 Guest.HostMemory) (values : List (HolWordLab 64))
    (run : evalCrepSemHOLProgExact {entryCrepState entry base capacity with clock := fuel}
      (.call none baselineCrepStart []) = (some (.return values),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + baselineCrepExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨extra,extraSmall,loopResult,loopPost,loopRun,loopState,same⟩ :=
    baseline_crep_loop_entry_bounded entry base capacity words fuel (some (.return values)) post run (by simp)
  simp only [Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop] at same
  subst loopResult
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    baseline_loop_return_native entry base capacity related (fuel + extra) loopPost (values.map wlabWlocExact) loopRun
  have monotone := baselineNativeFuel_mono (fuel + extra) (fuel + baselineCrepExtraFuel fuel) (by omega)
  have ffi : post.ffi = loopPost.ffi := loopState.2.2.2.2.1
  rw [← ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,Nat.le_trans bound monotone,nativeRun,observation⟩

#print axioms baseline_crep_return_native
/-- Actual Crep entry execution composes through the checked compiler pipeline
into a uniform native-step ceiling, retaining the original resource alternative. -/
theorem baseline_crep_ffi_native {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (base capacity : BitVec 64)
    (related : loopToWordStateRelHOLExact (entryLoopState entry base capacity) (entryFrontendState entry))
    (words : noLabelsHOL (entryFrontendState entry).memory
      (fun address => (entryFrontendState entry).mdomain address = true))
    (fuel : Nat) (post : CrepSemHOLState 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : evalCrepSemHOLProgExact {entryCrepState entry base capacity with clock := fuel}
      (.call none baselineCrepStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel (fuel + baselineCrepExtraFuel fuel) ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨extra,extraSmall,loopResult,loopPost,loopRun,loopState,same⟩ :=
    baseline_crep_loop_entry_bounded entry base capacity words fuel (some (.finalFfi event)) post run (by simp)
  simp only [Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop] at same
  subst loopResult
  obtain ⟨wordPost,final,outcome,count,native,bound,nativeRun,observation⟩ :=
    baseline_loop_ffi_native entry base capacity related (fuel + extra) loopPost event loopRun
  have monotone := baselineNativeFuel_mono (fuel + extra) (fuel + baselineCrepExtraFuel fuel) (by omega)
  have ffi : post.ffi = loopPost.ffi := loopState.2.2.2.2.1
  rw [← ffi] at observation
  exact ⟨wordPost,final,outcome,count,native,Nat.le_trans bound monotone,nativeRun,observation⟩

#print axioms baseline_crep_ffi_native
end InitECandidate.Runtime
