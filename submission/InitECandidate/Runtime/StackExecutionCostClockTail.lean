import InitECandidate.Runtime.StackExecutionCostClockLoop
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem stackCost_addClock_tail {F : Type} (price : HolProg 64 → Nat) (dest : Sum Nat Nat)
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F) result
    (run : StackSemEvaluate.evaluate (.call none dest none, source) = (result, post))
    (notTimeout : result ≠ some .timeOut)
    (bodyStable : ∀ body middle bodyResult,
      StackSemControl.findCode dest source.regs source.code = some body → source.clock ≠ 0 →
      StackSemEvaluate.evaluate (body, StackSemStateOps.decClock source) = (bodyResult, middle) →
      bodyResult ≠ some .timeOut → ∀ extra,
      stackExecutionCost (fun p _ => price p) body
        {StackSemStateOps.decClock source with clock := (StackSemStateOps.decClock source).clock + extra} =
        stackExecutionCost (fun p _ => price p) body (StackSemStateOps.decClock source))
    (extra : Nat) :
    stackExecutionCost (fun p _ => price p) (.call none dest none) {source with clock := source.clock + extra} =
      stackExecutionCost (fun p _ => price p) (.call none dest none) source := by
  rw [stackExecutionCost.eq_6 (fun p _ => price p) {source with clock := source.clock + extra} dest none,
    stackExecutionCost.eq_6 (fun p _ => price p) source dest none]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [StackSemEvaluate.evaluate_call] at run
  cases found : StackSemControl.findCode dest source.regs source.code with
  | none =>
    simp only [found]
    split <;> split <;> rfl
  | some body =>
    simp only [found] at run
    have positive : source.clock ≠ 0 := by
      intro zero
      rw [if_pos zero] at run
      exact notTimeout (Prod.mk.inj run).1.symm
    have shiftedPositive : source.clock + extra ≠ 0 := by omega
    simp only [positive, shiftedPositive, ↓reduceIte, found]
    rw [if_neg positive, StackSemEvaluateClock.fixClockEvaluate] at run
    rcases bodyRun : StackSemEvaluate.evaluate (body, StackSemStateOps.decClock source) with ⟨bodyResult, middle⟩
    rw [bodyRun] at run
    have bodyNotTimeout : bodyResult ≠ some .timeOut := by
      intro eq
      rw [eq] at run
      simp only [StackSemControl.badFunReturn, Bool.false_eq_true, ↓reduceIte] at run
      exact notTimeout (Prod.mk.inj run).1.symm
    rw [StackProps.EvaluateAddClock.decClock_addClock source extra positive]
    rw [bodyStable body middle bodyResult found positive bodyRun bodyNotTimeout extra]

#print axioms stackCost_addClock_tail
end InitECandidate.Runtime.StackToLab
