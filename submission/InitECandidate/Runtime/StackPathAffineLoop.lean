import InitECandidate.Runtime.StackPathAffineControl
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemControl Flapjack.StackSemStateOps

/-- Each continuing loop tick pays for the finished body's syntax potential.
Clock consumption telescopes across actual body execution and reentry. -/
theorem pathWork_loop_affine {width : Nat} [NeZero width] {C F : Type}
    (rate : Nat) (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (funding : 2 * sizeOf body + 2 ≤ rate)
    (first : AffinePathBound rate body s)
    (next : ∀ result middle, StackSemEvaluate.evaluate (body, s) = (result, middle) →
      contLoop result = true → middle.clock ≠ 0 → AffinePathBound rate (.loop body) (decClock middle)) :
    AffinePathBound rate (.loop body) s := by
  intro result post run notError
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at run
  cases bodyRun : StackSemEvaluate.evaluate (body, s) with
  | mk bodyResult middle =>
    rw [bodyRun] at run
    dsimp only at run
    have bodyNotError : bodyResult ≠ some .error := by
      intro eq
      rw [eq] at run
      simp only [contLoop, Flapjack.StackSemControl.exitLoop, Bool.false_eq_true, if_false] at run
      exact notError (Prod.mk.inj run).1.symm
    have bodyBound := first bodyResult middle bodyRun bodyNotError
    have bodyClock := StackSemEvaluateClock.evaluateClock body s bodyResult middle bodyRun
    have syntaxBound : 2 + 2 * sizeOf body ≤ 2 * sizeOf (.loop body : HolProg width) := by
      simp_wf; omega
    by_cases continuing : contLoop bodyResult = true
    · rw [if_pos continuing] at run
      by_cases zero : middle.clock = 0
      · rw [if_pos zero] at run
        simp only [Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        rw [pathWork, StackSemEvaluateClock.fixClockEvaluate, bodyRun]
        simp [continuing, zero]
        simp only [emptyEnv] at bodyBound ⊢
        omega
      · rw [if_neg zero] at run
        have nextBound := next bodyResult middle bodyRun continuing zero result post run notError
        have nextClock := StackSemEvaluateClock.evaluateClock (.loop body) (decClock middle) result post run
        have elapsed : s.clock - post.clock =
            (s.clock - middle.clock) + 1 + ((decClock middle).clock - post.clock) := by
          simp only [decClock] at nextClock ⊢
          omega
        rw [pathWork, StackSemEvaluateClock.fixClockEvaluate, bodyRun]
        simp only [continuing, Bool.true_and, bne_iff_ne, if_pos zero]
        rw [elapsed, Nat.mul_add, Nat.mul_add, Nat.mul_one]
        omega
    · rw [if_neg continuing] at run
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      have stopped : contLoop bodyResult = false := by simpa using continuing
      rw [pathWork, StackSemEvaluateClock.fixClockEvaluate, bodyRun]
      simp [stopped]
      omega

#print axioms pathWork_loop_affine
end InitECandidate.Runtime.StackToLab
