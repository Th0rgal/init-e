import InitECandidate.Runtime.StackExecutionCostClockTail
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem stackCost_addClock_raw {F : Type} (price : HolProg 64 → Nat) (dest : Nat)
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F) result
    (run : StackSemEvaluate.evaluate (.rawCall dest, source) = (result, post))
    (notTimeout : result ≠ some .timeOut)
    (bodyStable : ∀ prologue body middle bodyResult,
      sptLookup dest source.code = some (.seq prologue body) → source.clock ≠ 0 →
      StackSemEvaluate.evaluate (body, StackSemStateOps.decClock source) = (bodyResult, middle) →
      bodyResult ≠ some .timeOut → ∀ extra,
      stackExecutionCost (fun p _ => price p) body
        {StackSemStateOps.decClock source with clock := (StackSemStateOps.decClock source).clock + extra} =
        stackExecutionCost (fun p _ => price p) body (StackSemStateOps.decClock source))
    (extra : Nat) :
    stackExecutionCost (fun p _ => price p) (.rawCall dest) {source with clock := source.clock + extra} =
      stackExecutionCost (fun p _ => price p) (.rawCall dest) source := by
  rw [stackExecutionCost.eq_5 (fun p _ => price p) {source with clock := source.clock + extra} dest,
    stackExecutionCost.eq_5 (fun p _ => price p) source dest]
  rw [StackSemEvaluate.evaluate_rawCall] at run
  cases found : sptLookup dest source.code with
  | none =>
    simp only [found]
    split <;> split <;> rfl
  | some stored =>
    cases stored <;> simp only [StackSemControl.destSeq, found] at run ⊢
    all_goals try (split <;> split <;> rfl)
    rename_i prologue body
    have positive : source.clock ≠ 0 := by
      intro zero
      rw [if_pos zero] at run
      exact notTimeout (Prod.mk.inj run).1.symm
    have shiftedPositive : source.clock + extra ≠ 0 := by omega
    simp only [positive, shiftedPositive, ↓reduceIte]
    rw [if_neg positive] at run
    rcases bodyRun : StackSemEvaluate.evaluate (body, StackSemStateOps.decClock source) with ⟨bodyResult, middle⟩
    rw [bodyRun] at run
    have bodyNotTimeout : bodyResult ≠ some .timeOut := by
      intro eq
      rw [eq] at run
      simp only [StackSemControl.badFunReturn, Bool.false_eq_true, ↓reduceIte] at run
      exact notTimeout (Prod.mk.inj run).1.symm
    rw [StackProps.EvaluateAddClock.decClock_addClock source extra positive]
    rw [bodyStable prologue body middle bodyResult found positive bodyRun bodyNotTimeout extra]

#print axioms stackCost_addClock_raw
end InitECandidate.Runtime.StackToLab
