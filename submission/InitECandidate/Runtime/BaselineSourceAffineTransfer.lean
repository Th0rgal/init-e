import InitECandidate.Runtime.EndpointCanonicalLowering
import InitECandidate.Runtime.SourceTerminatesInstalled
import InitECandidate.Runtime.CanonicalAffineClosedForm
import InitECandidate.Runtime.BootstrappedMatchingBudget
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.RiscV.Target

/-- The actual submitted bootstrap and compiler transfer original Pancake
call/loop fuel to target evaluator steps with explicit fixed affine constants.
Every input and covered terminating result is included. -/
theorem baseline_source_affine_transfer :
    AffineTransfer baselineSubmission sourceNativeSlope (sourceNativeOffset + 46240) := by
  intro input outcome events fuel source covered sourceRun
  obtain ⟨boot, entry, bootBound, shift, endpointRelated⟩ := full_bootstrap_bounded
    (sourceFfi input) (baselineInitialState input) (baselineInitialState_related input)
  obtain ⟨result, sourcePost, run, terminal, trace⟩ := sourceTerminatesAt_installed
    input outcome events fuel (endpoint_canonicalOriginalSourceEntry input entry endpointRelated)
    (endpoint_canonical_original_declarations_evaluate input entry endpointRelated) sourceRun
  have nativeRun : ∃ steps targetOutcome native finalFfi,
      steps ≤ sourceNativeSlope * fuel + sourceNativeOffset ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) steps entry =
        (.halt targetOutcome, native, finalFfi) := by
    cases result with
    | error => cases terminal
    | timeOut => cases terminal
    | «break» => cases terminal
    | «continue» => cases terminal
    | exception exceptionId value => cases terminal
    | returned value =>
      obtain ⟨wordPost, final, targetOutcome, steps, native, bound, evaluated, observation⟩ :=
        endpoint_canonical_original_return_native_affine input entry endpointRelated fuel sourcePost value
          (by simpa only [FrontendStages.Declarations.globalStart] using run)
      exact ⟨steps, targetOutcome, native, final.ffi,
        bound.trans (sourceNativeFuel_affine fuel), evaluated⟩
    | finalFfi event =>
      obtain ⟨wordPost, final, targetOutcome, steps, native, bound, evaluated, observation⟩ :=
        endpoint_canonical_original_ffi_native_affine input entry endpointRelated fuel sourcePost event
          (by simpa only [FrontendStages.Declarations.globalStart] using run)
      exact ⟨steps, targetOutcome, native, final.ffi,
        bound.trans (sourceNativeFuel_affine fuel), evaluated⟩
  obtain ⟨steps, targetOutcome, native, finalFfi, bound, evaluated⟩ := nativeRun
  obtain ⟨count, countBound, matching⟩ := bootstrapped_matching_budget input outcome events source covered
    boot steps (sourceNativeSlope * fuel + sourceNativeOffset) entry native finalFfi
    bootBound bound shift targetOutcome evaluated
  exact ⟨count, by simpa only [Nat.add_assoc] using countBound, matching⟩
end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.baseline_source_affine_transfer
#check InitECandidate.Runtime.baseline_source_affine_transfer
