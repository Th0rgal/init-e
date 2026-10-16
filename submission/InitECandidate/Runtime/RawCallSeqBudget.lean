import InitECandidate.Runtime.RawCallIfBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Standard

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase

abbrev SeqSecondIH {width : Nat} [NeZero width] (C F : Type)
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ middle : StackSemStateFiniteExact width C F,
    StackSemEvaluate.evaluate (first, source) = (none, middle) →
    ProgramIH C F second middle

/-- Complete standard composition in original175-194, before the compiler's
optimized Seq split. This source-local proof infrastructure has no separately
named HOL declaration, so carries no comp_correct tag. Its target is the actual
standard compiled Seq: the full parent still needs the optimized equal/less/
greater frame branches and the assembling theorem. Only the actual first and
guarded second evaluate_ind hypotheses supplement the original three premises.
Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
theorem simulateStandardSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ProgramIH C F first source)
    (secondIH : SeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (.seq (comp info first) (comp info second)) info target post result
      (source.clock - post.clock) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
      rw [evaluateSeqUnclamped, firstRun] at execution
      obtain ⟨firstClock, firstBound, targetMiddle, firstSpace, middleRelation, firstTargetRun, firstGuard⟩ :=
        firstIH info target middle none ⟨firstRun, by simp, relation⟩
      have spaceEq := firstGuard (by simp)
      subst firstSpace
      have spaceSelf : { targetMiddle with stackSpace := targetMiddle.stackSpace } =
          targetMiddle := by cases targetMiddle; rfl
      rw [spaceSelf] at firstTargetRun
      obtain ⟨secondClock, secondBound, targetPost, finalSpace, postRelation, secondTargetRun, finalGuard⟩ :=
        secondIH middle firstRun info targetMiddle post result
          ⟨execution, nonerror, middleRelation⟩
      have extendedFirst := Compiler.Backend.StackProps.evaluateAddClock secondClock
        (comp info first) { target with clock := target.clock + firstClock }
        none targetMiddle ⟨firstTargetRun, by simp⟩
      have inputEq : { { target with clock := target.clock + firstClock } with
          clock := ({ target with clock := target.clock + firstClock }).clock + secondClock } =
          { target with clock := target.clock + (firstClock + secondClock) } := by
        simp only [Nat.add_assoc]
      rw [inputEq] at extendedFirst
      have firstConsumes := StackSemEvaluateClock.evaluateClock first source none middle firstRun
      have secondConsumes := StackSemEvaluateClock.evaluateClock second middle result post execution
      have firstAllowance := clockAllowance_le first source.clock middle.clock
      have secondAllowance := clockAllowance_le second middle.clock post.clock
      refine ⟨firstClock + secondClock, by omega, targetPost, finalSpace, postRelation, ?_, finalGuard⟩
      rw [evaluateSeqUnclamped, extendedFirst]
      exact secondTargetRun
  | some firstResult =>
      rw [evaluateSeqUnclamped, firstRun] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      obtain ⟨clock, clockBound, targetPost, finalSpace, postRelation, targetRun, guard⟩ :=
        firstIH info target middle (some firstResult) ⟨firstRun, nonerror, relation⟩
      refine ⟨clock, Nat.le_trans clockBound (clockAllowance_le _ _ _), targetPost, finalSpace, postRelation, ?_, guard⟩
      rw [evaluateSeqUnclamped, targetRun]


#print axioms simulateStandardSeq
end InitECandidate.Runtime.StackRawCall
