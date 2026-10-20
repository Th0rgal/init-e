import InitECandidate.Runtime.StackRemoveExecutedSimulation
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

#print axioms stackExecutionCost_call_run
end InitECandidate.Runtime.StackToLab
