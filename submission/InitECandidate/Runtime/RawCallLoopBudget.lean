import InitECandidate.Runtime.RawCallIfBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Loop

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.LoopCase

/-! Loop simulation charged to actual consumed source clock, including timeout,
exit and guarded reentry, with the full original relation and exceptions. -/
theorem compCorrectLoopExit {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : ProgramIH C F body source)
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target)
    (exit : contLoop result = false) :
    BoundedSimulationResult (comp info (.loop body)) info target post
      (StackSemControl.exitLoop result) (source.clock - post.clock) := by
  obtain ⟨clock, clockBound, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
    bodyIH info target post result ⟨execution, nonerror, relation⟩
  refine ⟨clock, Nat.le_trans clockBound (clockAllowance_le _ _ _), targetState, stackSpace, postRelation, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclamped, targetExecution]
    simp only [exit, Bool.false_eq_true, if_false]
  · intro exitGuard
    exact guard (exitLoopGuard result exitGuard)

/-- Loop continuation excludes both exceptional stack-space guard results. -/
theorem contLoopGuard {width : Nat} [NeZero width]
    (result : Option (StackSemResult width)) (continuing : contLoop result = true) :
    result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) := by
  rcases Compiler.Backend.StackProps.contLoopImp result continuing with h | h <;>
    simp [h]

/-- The zero-clock continuation branch, with target timeout and relation
both derived from the actual body induction hypothesis. Untagged case support. -/
theorem compCorrectLoopTimeout {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : ProgramIH C F body source)
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target)
    (continuing : contLoop result = true) (zero : post.clock = 0) :
    BoundedSimulationResult (comp info (.loop body)) info target (emptyEnv post)
      (some .timeOut) (source.clock - post.clock) := by
  obtain ⟨clock, clockBound, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
    bodyIH info target post result ⟨execution, nonerror, relation⟩
  have spaceEq := guard (contLoopGuard result continuing)
  subst stackSpace
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  rw [stackSelf] at targetExecution
  have targetZero : targetState.clock = 0 :=
    (stateRel_clock info post targetState postRelation).trans zero
  refine ⟨clock, Nat.le_trans clockBound (clockAllowance_le _ _ _), emptyEnv targetState, (emptyEnv targetState).stackSpace,
    stateRel_emptyEnv info post targetState postRelation, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclamped, targetExecution]
    simp only [continuing, if_true]
    rw [if_pos targetZero]
  · intro impossible
    exact False.elim (impossible.1 rfl)

/-- The original evaluate_ind Loop reentry IH at the actual body's post-state.
The source body evaluation, continuation and nonzero post-clock guard the
motive at decClock bodyPost; no arbitrary smaller-clock state is quantified. -/
abbrev LoopReentryIH {width : Nat} [NeZero width] (C F : Type)
    (body : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (bodyResult : Option (StackSemResult width))
    (bodyPost : StackSemStateFiniteExact width C F),
    StackSemEvaluate.evaluate (body, source) = (bodyResult, bodyPost) →
    contLoop bodyResult = true → bodyPost.clock ≠ 0 →
    ProgramIH C F (.loop body) (decClock bodyPost)

/-- Nonzero continuation: extend the actual target body clock by the clock
needed for the smaller recursive Loop execution. All target results are derived
from the two genuine IHs. Untagged case-split infrastructure. -/
theorem compCorrectLoopReentry {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target bodyPost post : StackSemStateFiniteExact width C F)
    (bodyResult result : Option (StackSemResult width))
    (bodyIH : ProgramIH C F body source)
    (reentryIH : LoopReentryIH C F body source)
    (bodyExecution : StackSemEvaluate.evaluate (body, source) = (bodyResult, bodyPost))
    (bodyNonerror : bodyResult ≠ some .error) (relation : stateRel info source target)
    (continuing : contLoop bodyResult = true) (nonzero : bodyPost.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate (.loop body, decClock bodyPost) = (result, post))
    (nonerror : result ≠ some .error) :
    BoundedSimulationResult (comp info (.loop body)) info target post result (source.clock - post.clock) := by
  obtain ⟨clock, clockBound, targetBody, stackSpace, bodyRelation, targetBodyExecution, bodyGuard⟩ :=
    bodyIH info target bodyPost bodyResult ⟨bodyExecution, bodyNonerror, relation⟩
  have continuationGuard := contLoopGuard bodyResult continuing
  have spaceEq := bodyGuard continuationGuard
  subst stackSpace
  have stackSelf : { targetBody with stackSpace := targetBody.stackSpace } = targetBody := by
    cases targetBody
    rfl
  rw [stackSelf] at targetBodyExecution
  have recursiveRelation := stateRel_decClock info bodyPost targetBody bodyRelation
  obtain ⟨recursiveClock, recursiveBound, targetPost, finalSpace, postRelation, targetExecution, guard⟩ :=
    reentryIH bodyResult bodyPost bodyExecution continuing nonzero
      info (decClock targetBody) post result
      ⟨execution, nonerror, recursiveRelation⟩
  have targetClockEq := stateRel_clock info bodyPost targetBody bodyRelation
  have targetNonzero : targetBody.clock ≠ 0 := by
    simpa only [targetClockEq] using nonzero
  have extendedBody := Compiler.Backend.StackProps.evaluateAddClock recursiveClock
    (comp info body) { target with clock := target.clock + clock }
    bodyResult targetBody ⟨targetBodyExecution, continuationGuard.1⟩
  have inputEq : { { target with clock := target.clock + clock } with
      clock := ({ target with clock := target.clock + clock }).clock + recursiveClock } =
      { target with clock := target.clock + (clock + recursiveClock) } := by
    simp only [Nat.add_assoc]
  rw [inputEq] at extendedBody
  have reentryEq : decClock { targetBody with clock := targetBody.clock + recursiveClock } =
      { decClock targetBody with clock := (decClock targetBody).clock + recursiveClock } := by
    simp only [decClock]
    congr 1
    omega
  have bodyConsumes := StackSemEvaluateClock.evaluateClock body source bodyResult bodyPost bodyExecution
  have recursiveConsumes := StackSemEvaluateClock.evaluateClock (.loop body) (decClock bodyPost) result post execution
  have bodyAllowance := clockAllowance_le body source.clock bodyPost.clock
  change recursiveClock ≤ bodyPost.clock - 1 - post.clock at recursiveBound
  change post.clock ≤ bodyPost.clock - 1 at recursiveConsumes
  refine ⟨clock + recursiveClock, by omega, targetPost, finalSpace, postRelation, ?_, guard⟩
  rw [comp, evaluateLoopUnclamped, extendedBody]
  simp only [continuing, if_true]
  rw [if_neg (show targetBody.clock + recursiveClock ≠ 0 by omega), reentryEq]
  exact targetExecution

/-- Genuine recursive Loop case. The original three premises are retained;
only the body IH at the fixed source and actual guarded body-post reentry IH
are added. Both original compTop/comp existential conclusions remain intact.
The full native evaluator inherits its documented real-carrier assurance limit;
this proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectLoop {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : ProgramIH C F body source)
    (reentryIH : LoopReentryIH C F body source)
    (hypothesis : StackSemEvaluate.evaluate (.loop body, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.loop body)) info target post result (source.clock - post.clock) ∧
    BoundedSimulationResult (comp info (.loop body)) info target post result (source.clock - post.clock) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have bodyNonerror := loopBodyNonError body source post result execution nonerror
  have same : compTop info (.loop body) = comp info (.loop body) := rfl
  rw [same]
  suffices simulation : BoundedSimulationResult (comp info (.loop body)) info target post result (source.clock - post.clock) by
    exact ⟨simulation, simulation⟩
  rw [evaluateLoopUnclamped] at execution
  rcases bodyExecution : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, bodyPost⟩
  rw [bodyExecution] at execution bodyNonerror
  change bodyResult ≠ some .error at bodyNonerror
  by_cases continuing : contLoop bodyResult = true
  · simp only [continuing, if_true] at execution
    by_cases zero : bodyPost.clock = 0
    · rw [if_pos zero] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact compCorrectLoopTimeout body info source target bodyPost bodyResult bodyIH
        bodyExecution bodyNonerror relation continuing zero
    · rw [if_neg zero] at execution
      exact compCorrectLoopReentry body info source target bodyPost post bodyResult result
        bodyIH reentryIH bodyExecution bodyNonerror relation continuing zero execution nonerror
  · have exit : contLoop bodyResult = false := by
      cases h : contLoop bodyResult <;> simp_all
    simp only [exit, Bool.false_eq_true, if_false] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    exact compCorrectLoopExit body info source target bodyPost bodyResult bodyIH
      bodyExecution bodyNonerror relation exit


#print axioms compCorrectLoop
end InitECandidate.Runtime.StackRawCall
