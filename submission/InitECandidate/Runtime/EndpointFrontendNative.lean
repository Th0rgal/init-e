import InitECandidate.Runtime.EndpointRuntimeEntry
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
noncomputable def endpointFrontendState {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :=
  {entryWordState entry.cfg entry.source with code := sptFromAList FrontendStages.pass5}

theorem endpointFrontendState_gc {input : Guest.InputBlob} (entry : EndpointRuntimeEntry input endpoint) :
    WordSimp.gcFunConstOk (endpointFrontendState entry).gcFun :=
  DataToWord.Proofs.Gc.gcFunConstOkWordGcFun (c := baselineCompilerConfig.dataConf)

/-- Concrete baseline initialization discharges all optimizer state premises.
The exact initial fuel, result, trace, remaining clock and stack accounting survive. -/
theorem endpoint_frontend_optimized_run {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat)
    (result : Option (WordSemResult 64))
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {endpointFrontendState entry with clock := fuel} = (result,post))
    (notError : result ≠ some .error) :
    ∃ final, WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (result,final) ∧
      final.ffi = post.ffi ∧ final.clock = post.clock ∧ final.stackMax = post.stackMax ∧
      final.stackLimit = post.stackLimit := by
  obtain ⟨final, evaluated, ffi, clock, stack⟩ := baseline_optimizer_run
    (endpointFrontendState entry) fuel result post rfl (endpointFrontendState_gc entry) rfl run notError
  have actual : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (result,final) := evaluated
  have sourceLimit := (WordSemStateFiniteExact.evaluate_consts _ _ _ _ run).2.2.2.2.2
  have targetLimit := (WordSemStateFiniteExact.evaluate_consts _ _ _ _ actual).2.2.2.2.2
  exact ⟨final,actual,ffi,clock,stack,targetLimit.symm.trans sourceLimit⟩

#print axioms endpointFrontendState_gc
#print axioms endpoint_frontend_optimized_run
end InitECandidate.Runtime
