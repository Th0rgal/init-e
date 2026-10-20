import InitECandidate.Runtime.StackExecutionCostProps
import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Loop cost stability follows the actual reached body and recursive reentry.
Both hypotheses are cost induction obligations, not native execution budgets. -/
theorem stackCost_addClock_loop {F : Type} (price : HolProg 64 → Nat) (body : HolProg 64)
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F) result
    (run : StackSemEvaluate.evaluate (.loop body, source) = (result, post))
    (notTimeout : result ≠ some .timeOut)
    (bodyStable : ∀ middle bodyResult,
      StackSemEvaluate.evaluate (body, source) = (bodyResult, middle) → bodyResult ≠ some .timeOut →
      ∀ extra, stackExecutionCost (fun p _ => price p) body {source with clock := source.clock + extra} =
        stackExecutionCost (fun p _ => price p) body source)
    (restStable : ∀ middle bodyResult,
      StackSemEvaluate.evaluate (body, source) = (bodyResult, middle) →
      StackSemControl.contLoop bodyResult = true → middle.clock ≠ 0 →
      StackSemEvaluate.evaluate (.loop body, StackSemStateOps.decClock middle) = (result, post) →
      ∀ extra, stackExecutionCost (fun p _ => price p) (.loop body)
        {StackSemStateOps.decClock middle with clock := (StackSemStateOps.decClock middle).clock + extra} =
        stackExecutionCost (fun p _ => price p) (.loop body) (StackSemStateOps.decClock middle))
    (extra : Nat) :
    stackExecutionCost (fun p _ => price p) (.loop body) {source with clock := source.clock + extra} =
      stackExecutionCost (fun p _ => price p) (.loop body) source := by
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at run
  rcases bodyRun : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, middle⟩
  rw [bodyRun] at run
  dsimp only at run
  have bodyNotTimeout : bodyResult ≠ some .timeOut := by
    intro eq
    rw [eq] at run
    simp only [StackSemControl.contLoop, Bool.false_eq_true, ↓reduceIte, StackSemControl.exitLoop] at run
    exact notTimeout (Prod.mk.inj run).1.symm
  have shifted := StackProps.evaluateAddClock extra body source bodyResult middle ⟨bodyRun, bodyNotTimeout⟩
  rw [stackExecutionCost.eq_3 (fun p _ => price p) {source with clock := source.clock + extra} body,
    stackExecutionCost.eq_3 (fun p _ => price p) source body]
  simp only [StackSemEvaluateClock.fixClockEvaluate]
  simp only [bodyRun, shifted]
  rw [bodyStable middle bodyResult bodyRun bodyNotTimeout extra]
  by_cases continues : StackSemControl.contLoop bodyResult = true
  · rw [if_pos continues] at run
    have positive : middle.clock ≠ 0 := by
      intro zero
      rw [if_pos zero] at run
      exact notTimeout (Prod.mk.inj run).1.symm
    rw [if_neg positive] at run
    have positiveShift : middle.clock + extra ≠ 0 := by omega
    simp only [continues, Bool.true_and, bne_iff_ne, positive, positiveShift, ↓reduceIte]
    simp only [if_pos positiveShift, if_pos positive]
    rw [StackProps.EvaluateAddClock.decClock_addClock middle extra positive]
    exact congrArg (fun work => price (.loop body) + stackExecutionCost (fun p _ => price p) body source + work)
      (restStable middle bodyResult bodyRun continues positive run extra)
  · have stopped : StackSemControl.contLoop bodyResult = false := Bool.eq_false_iff.mpr continues
    simp only [stopped, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

#print axioms stackCost_addClock_loop
end InitECandidate.Runtime.StackToLab
