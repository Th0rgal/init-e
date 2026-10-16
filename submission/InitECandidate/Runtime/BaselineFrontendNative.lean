import InitECandidate.Runtime.BaselineOptimizerRuns
import InitECandidate.Runtime.BaselineNativeFuel
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

/-- The actual initialized Word state before replacing its frontend code by
the compiler-certified optimized code. All other entry fields are shared. -/
noncomputable def entryFrontendState {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :=
  {entryWordState entry.cfg entry.source with code := sptFromAList FrontendStages.pass5}

theorem entryFrontendState_gc {input : Guest.InputBlob} (entry : BaselineRuntimeEntry input) :
    WordSimp.gcFunConstOk (entryFrontendState entry).gcFun :=
  DataToWord.Proofs.Gc.gcFunConstOkWordGcFun (c := baselineCompilerConfig.dataConf)

/-- Concrete baseline initialization discharges all optimizer state premises.
The exact initial fuel, result, trace, remaining clock and stack accounting survive. -/
theorem baseline_frontend_optimized_run {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (result : Option (WordSemResult 64))
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryFrontendState entry with clock := fuel} = (result,post))
    (notError : result ≠ some .error) :
    ∃ final, WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (result,final) ∧
      final.ffi = post.ffi ∧ final.clock = post.clock ∧ final.stackMax = post.stackMax ∧
      final.stackLimit = post.stackLimit := by
  obtain ⟨final, evaluated, ffi, clock, stack⟩ := baseline_optimizer_run
    (entryFrontendState entry) fuel result post rfl (entryFrontendState_gc entry) rfl run notError
  have actual : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (result,final) := evaluated
  have sourceLimit := (WordSemStateFiniteExact.evaluate_consts _ _ _ _ run).2.2.2.2.2
  have targetLimit := (WordSemStateFiniteExact.evaluate_consts _ _ _ _ actual).2.2.2.2.2
  exact ⟨final,actual,ffi,clock,stack,targetLimit.symm.trans sourceLimit⟩

/-- An actual pre-optimization Word return has a native step bound depending
only on initial fuel and fixed compiled-program constants. -/
theorem baseline_frontend_return_native {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (values : List (WordLocW 64))
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryFrontendState entry with clock := fuel} = (some (.result (.loc 1 0) values),post)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  obtain ⟨optimized, evaluated, ffi, _, stack, limit⟩ :=
    baseline_frontend_optimized_run entry fuel _ post run (by simp)
  obtain ⟨final,outcome,count,native,bound,nativeRun,observation⟩ :=
    baseline_word_return_native_uniform entry fuel optimized values evaluated
  rw [ffi,stack,limit] at observation
  exact ⟨final,outcome,count,native,bound,nativeRun,observation⟩

#print axioms entryFrontendState_gc
#print axioms baseline_frontend_optimized_run
#print axioms baseline_frontend_return_native
end InitECandidate.Runtime
