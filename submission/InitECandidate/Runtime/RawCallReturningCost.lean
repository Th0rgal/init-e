import InitECandidate.Runtime.RawCallExecutedReturningCallee

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open InitECandidate.Runtime.StackToLab

/-- Exact returning-call counter decomposition at its actual successful
lookup and body run. Invalid return locations charge no continuation, just
as in the source counter; the semantic simulation must reject them separately. -/
theorem returning_executionCost_eq {F : Type} (price : HolProg 64 → Nat)
    (ret : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (program : HolProg 64) (bodyResult : Option (StackSemResult 64))
    (lookup : findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (bodyRun : StackSemEvaluate.evaluate
      (program, decClock (setVar link (.loc l1 l2) source)) = (bodyResult, middle)) :
    stackExecutionCost (fun p _ => price p) (.call (some (ret, link, l1, l2)) dest handler) source =
      stackExecutionCost (fun p _ => price p) program (decClock (setVar link (.loc l1 l2) source)) +
      selectedContinuationBudget bodyResult l1 l2 handler
        (stackExecutionCost (fun p _ => price p) ret middle)
        (match handler with | none => 0 | some (hp, _, _) => stackExecutionCost (fun p _ => price p) hp middle) +
      price (.call (some (ret, link, l1, l2)) dest handler) := by
  rw [stackExecutionCost]
  simp only [nonzero, if_false, lookup]
  rw [StackSemEvaluateClock.fixClockEvaluate, bodyRun]
  cases handler <;> rfl

#print axioms returning_executionCost_eq
end InitECandidate.Runtime.StackRawCall
