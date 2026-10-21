import InitECandidate.Runtime.StackCallRunCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target

variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- Free sequence nodes permit reassociation without changing reached work,
including executions that stop before the final suffix. -/
theorem stackCost_seq_assoc {F : Type} (first second third : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p)
      (.seq (.seq first second) third) source =
    stackExecutionCost (fun p _ => price p)
      (.seq first (.seq second third)) source := by
  have free : ∀ a b : HolProg 64, price (.seq a b) = 0 := ConservativeRemovalPrice.freeSeq
  simp only [stackExecutionCost_seq, free, Nat.zero_add,
    StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨result, middle⟩
  cases result with
  | some result => simp
  | none =>
    rcases secondRun : StackSemEvaluate.evaluate (second, middle) with ⟨result, post⟩
    cases result <;> simp [Nat.add_assoc]

/-- Pointwise suffix cost equality is preserved under the same prefix. -/
theorem stackCost_seq_congr_right {F : Type} (first second third : HolProg 64)
    (same : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => price p) second s =
      stackExecutionCost (fun p _ => price p) third s)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => price p) (.seq first second) source =
    stackExecutionCost (fun p _ => price p) (.seq first third) source := by
  rw [stackExecutionCost_seq, stackExecutionCost_seq]
  simp only [show price (.seq first second) = 0 from ConservativeRemovalPrice.freeSeq _ _,
    show price (.seq first third) = 0 from ConservativeRemovalPrice.freeSeq _ _, Nat.zero_add]
  rcases run : StackSemEvaluate.evaluate (first, source) with ⟨result, middle⟩
  cases result <;> simp only [same]

#print axioms stackCost_seq_congr_right

#print axioms stackCost_seq_assoc
end InitECandidate.Runtime.StackToLab
