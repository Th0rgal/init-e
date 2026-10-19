import InitECandidate.Runtime.NativeBudget
import InitECandidate.Proofs.FullBaseline
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.RiscV.L3

/-- Any actual bounded halt after the verified bootstrap has the required
challenge observation. Exact compiler correctness rules out a spurious resource halt. -/
theorem bootstrapped_matching_budget (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (covered : coveredOutcome outcome)
    (boot steps bound : Nat) (entry post : riscv_state)
    (finalFfi : HolFfiState Guest.HostMemory)
    (bootBound : boot ≤ 46240) (stepBound : steps ≤ bound)
    (shift : ∀ clock,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) (boot + clock)
        (baselineInitialState input) =
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock entry)
    (targetOutcome : HolOutcome)
    (run : evaluateTargetHOL baselineMachineConfig (sourceFfi input) steps entry =
      (.halt targetOutcome, post, finalFfi)) :
    ∃ count, count ≤ bound + 46240 ∧
      matchingExecutionAt baselineSubmission input outcome events count := by
  have fullRun : evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (boot + steps) (baselineInitialState input) =
      (.halt targetOutcome, post, finalFfi) := (shift steps).trans run
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  have behavior : machineSemHOL baselineMachineConfig (sourceFfi input)
      (baselineInitialState input) (.terminate targetOutcome finalFfi.ioEvents) :=
    ⟨boot + steps, post, finalFfi, fullRun, rfl⟩
  have same := (full_baseline_correct input nonfail _ behavior).trans source
  have outcomes := HolBehaviour.terminate.inj same
  refine ⟨boot + steps, by omega, targetOutcome, post, finalFfi, ?_, ?_⟩
  · simpa only [baselineSubmission_machineConfig, baselineSubmission_initialState] using fullRun
  · rw [outcomes.1, outcomes.2]
    exact matchingResult_refl input outcome events covered
end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.bootstrapped_matching_budget
