import InitECandidate.Runtime.StackRemoveExecutedSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallReturnNone
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps

/-- Returning-call cost after the actual lookup and callee evaluator run.
Only the continuation selected by the actual return/exception contributes. -/
theorem stackExecutionCost_call_run {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → Nat)
    (rp program : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F) result
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program)
    (run : StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (result, middle)) :
    stackExecutionCost price (.call (some (rp, link, l1, l2)) dest handler) source =
      stackExecutionCost price program (decClock (setVar link (.loc l1 l2) source)) +
      selectedContinuationBudget result l1 l2 handler (stackExecutionCost price rp middle)
        (match handler with | none => 0 | some (hp, _, _) => stackExecutionCost price hp middle) +
      price (.call (some (rp, link, l1, l2)) dest handler) source := by
  rw [stackExecutionCost.eq_7, if_neg positive, found]
  dsimp only
  rw [StackSemEvaluateClock.fixClockEvaluate, run]
  cases handler with
  | none => rfl
  | some packet =>
    rcases packet with ⟨hp, hs, hl⟩
    rfl

/-- The unused continuation allowance changes neither the reached callee path
nor its cost. Shared by normal returns and caught exceptions. -/
theorem stackExecutionCost_calleeAllowance {F : Type} (price : HolProg 64 → Nat)
    (program : HolProg 64) (target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (link l1 l2 first second : Nat) result (positive : target.clock ≠ 0)
    (run : StackSemEvaluate.evaluate (program,
      {decClock (setVar link (.loc l1 l2) target) with
        clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    stackExecutionCost (fun p _ => price p) program
      (decClock (setVar link (.loc l1 l2) {target with clock := (first + second) + target.clock})) =
    stackExecutionCost (fun p _ => price p) program
      {decClock (setVar link (.loc l1 l2) target) with
        clock := first + (decClock (setVar link (.loc l1 l2) target)).clock} := by
  rw [StackRemove.CompCorrect.CallReturnNone.entryClock target link l1 l2 (first + second) positive]
  have eq := stackExecutionCost_addClock price program
    {decClock (setVar link (.loc l1 l2) target) with
      clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}
    post result run notTimeout second
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using eq

#print axioms stackExecutionCost_calleeAllowance
#print axioms stackExecutionCost_call_run
end InitECandidate.Runtime.StackToLab
