import InitECandidate.Runtime.Bounds
import InitECandidate.Runtime.BootstrapBudget
import InitECandidate.Proofs.StartupEnvironment
import InitECandidate.Proofs.BaselineSubmissionDefinition

namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Remaining native compiler obligation, after initialization. It quantifies
every native-entry machine related to the verified compiler installation. -/
def NativeAffineTransfer (scale overhead : Nat) : Prop :=
  ∀ input outcome events fuel,
    sourceBehaviour input = .terminate outcome events → coveredOutcome outcome →
    sourceTerminatesAt input outcome events fuel →
    ∀ native, targetStateRel riscvTarget installedAsm native →
    ∃ steps, steps ≤ scale * fuel + overhead ∧
      ∃ targetOutcome post finalFfi,
        evaluateTargetHOL baselineMachineConfig (sourceFfi input) steps native =
          (.halt targetOutcome, post, finalFfi) ∧
        matchingResult input outcome events targetOutcome finalFfi.ioEvents

/-- The concrete bootstrap adds at most 46240 target steps to an independently
proved native compiler bound. No startup timing premise is left to discharge. -/
theorem affine_transfer_of_native (scale overhead : Nat)
    (nativeBound : NativeAffineTransfer scale overhead) :
    AffineTransfer baselineSubmission scale (overhead + 46240) := by
  intro input outcome events fuel source covered sourceRun
  obtain ⟨count, native, countBound, shift, installed⟩ := full_bootstrap_bounded
    (sourceFfi input) (baselineInitialState input) (baselineInitialState_related input)
  obtain ⟨steps, stepBound, targetOutcome, post, finalFfi, run, matching⟩ :=
    nativeBound input outcome events fuel source covered sourceRun native installed
  refine ⟨count + steps, ?_, targetOutcome, post, finalFfi, ?_, matching⟩
  · omega
  · rw [baselineSubmission_machineConfig, baselineSubmission_initialState, shift]
    exact run

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.affine_transfer_of_native
