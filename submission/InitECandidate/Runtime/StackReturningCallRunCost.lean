import InitECandidate.Runtime.StackCallRunCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Actual returning-call work includes only the continuation selected by
its callee result. This lemma exposes reached states for the semantic bridge;
it does not assume a global execution budget. -/
theorem stackCost_returning_call_run {F : Type}
    (continuation : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat)) (callee : HolProg 64)
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (clock : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some callee)
    (run : StackSemEvaluate.evaluate
      (callee, StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) = (result, post)) :
    stackExecutionCost (fun p _ => price p)
      (.call (some (continuation,link,l1,l2)) dest handler) source ≤
    stackExecutionCost (fun p _ => price p)
      callee (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) +
    selectedContinuationBudget result l1 l2 handler
      (stackExecutionCost (fun p _ => price p) continuation post)
      (match handler with
       | none => 0
       | some (body,_,_) => stackExecutionCost (fun p _ => price p) body post) + 12 := by
  rw [stackExecutionCost]
  simp only [clock, ↓reduceIte, found]
  rw [StackSemEvaluateClock.fixClockEvaluate, run]
  have localBound : price
      (.call (some (continuation,link,l1,l2)) dest handler) ≤ 12 := by
    exact (caps.le _).trans (by cases dest <;> simp [removalLocalPrice, nativePriceWithGap, callJumpWork])
  rcases handler with _ | ⟨handlerCode, h1, h2⟩ <;> dsimp only <;> omega

#print axioms stackCost_returning_call_run
end InitECandidate.Runtime.StackToLab
