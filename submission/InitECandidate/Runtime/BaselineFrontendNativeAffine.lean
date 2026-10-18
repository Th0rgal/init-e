import InitECandidate.Runtime.BaselineFrontendNative
import InitECandidate.Runtime.BaselineOptimizerRuns
import InitECandidate.Runtime.BaselineNativeFuel
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
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

/-- An actual pre-optimization Word return has a native step bound depending
only on initial fuel and fixed compiled-program constants. -/
theorem baseline_frontend_return_native_affine {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (values : List (WordLocW 64))
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryFrontendState entry with clock := fuel} = (some (.result (.loc 1 0) values),post)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  obtain ⟨optimized, evaluated, ffi, _, stack, limit⟩ :=
    baseline_frontend_optimized_run entry fuel _ post run (by simp)
  obtain ⟨final,outcome,count,native,bound,nativeRun,observation⟩ :=
    baseline_word_return_native_affine_bound entry fuel optimized values evaluated
  rw [ffi,stack,limit] at observation
  exact ⟨final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms baseline_frontend_return_native_affine
end InitECandidate.Runtime
