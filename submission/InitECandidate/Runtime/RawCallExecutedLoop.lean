import InitECandidate.Runtime.RawCallExecutedIf
import InitECandidate.Runtime.RawCallLoopBudget

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.LoopCase
open InitECandidate.Runtime.StackToLab

abbrev ExecutedLoopReentryIH {F : Type} (price : HolProg 64 → Nat)
    (body : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ bodyResult bodyPost,
    StackSemEvaluate.evaluate (body, source) = (bodyResult, bodyPost) →
    contLoop bodyResult = true → bodyPost.clock ≠ 0 →
    ExecutedProgramIH price (.loop body) (decClock bodyPost)

/-- All actual loop outcomes retain the source execution counter. The
continuing case recurses only at the actual post-body state and funds clock
extension through the proved execution-cost stability theorem. -/
theorem executed_loop {F : Type} (price : HolProg 64 → Nat)
    (body : HolProg 64) (info : Spt Nat)
    (samePrice : price (.loop (comp info body)) = price (.loop body))
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (bodyIH : ExecutedProgramIH price body source)
    (reentryIH : ExecutedLoopReentryIH price body source)
    (hypothesis : StackSemEvaluate.evaluate (.loop body, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult price (comp info (.loop body)) info target post result
      (stackExecutionCost (fun p _ => price p) (.loop body) source) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have bodyNonerror := loopBodyNonError body source post result execution nonerror
  rw [evaluateLoopUnclamped] at execution
  rcases bodyExecution : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, bodyPost⟩
  rw [bodyExecution] at execution bodyNonerror
  change bodyResult ≠ some .error at bodyNonerror
  change ExecutedSimulationResult price (.loop (comp info body)) info target post result _
  obtain ⟨clock, targetBody, stackSpace, bodyRelation, targetBodyExecution, bodyGuard, bodyCost⟩ :=
    bodyIH info target bodyPost bodyResult ⟨bodyExecution, bodyNonerror, relation⟩
  by_cases continuing : contLoop bodyResult = true
  · simp only [continuing, if_true] at execution
    have continuationGuard := contLoopGuard bodyResult continuing
    have spaceEq := bodyGuard continuationGuard
    subst stackSpace
    have stackSelf : {targetBody with stackSpace := targetBody.stackSpace} = targetBody := by
      cases targetBody; rfl
    rw [stackSelf] at targetBodyExecution
    have targetClockEq := stateRel_clock info bodyPost targetBody bodyRelation
    by_cases zero : bodyPost.clock = 0
    · rw [if_pos zero] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      have targetZero : targetBody.clock = 0 := targetClockEq.trans zero
      refine ⟨clock, emptyEnv targetBody, (emptyEnv targetBody).stackSpace,
        stateRel_emptyEnv info bodyPost targetBody bodyRelation, ?_, ?_, ?_⟩
      · rw [evaluateLoopUnclamped, targetBodyExecution]
        simp only [continuing, if_true]
        rw [if_pos targetZero]
      · intro impossible
        exact False.elim (impossible.1 rfl)
      · conv_lhs => rw [stackExecutionCost]
        conv_rhs => rw [stackExecutionCost]
        simp only [StackSemEvaluateClock.fixClockEvaluate]
        simp only [StackSemEvaluateClock.fixClockEvaluate, targetBodyExecution,
          bodyExecution, continuing, targetZero, zero, beq_self_eq_true,
          Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false,
          Nat.add_zero, samePrice]
        exact Nat.add_le_add_left bodyCost _
    · rw [if_neg zero] at execution
      have recursiveRelation := stateRel_decClock info bodyPost targetBody bodyRelation
      obtain ⟨recursiveClock, targetPost, finalSpace, postRelation, targetExecution, guard, recursiveCost⟩ :=
        reentryIH bodyResult bodyPost bodyExecution continuing zero
          info (decClock targetBody) post result ⟨execution, nonerror, recursiveRelation⟩
      have targetNonzero : targetBody.clock ≠ 0 := by simpa only [targetClockEq] using zero
      have extendedBody := StackProps.evaluateAddClock recursiveClock (comp info body)
        {target with clock := target.clock + clock} bodyResult targetBody
          ⟨targetBodyExecution, continuationGuard.1⟩
      have stable := stackExecutionCost_addClock price (comp info body)
        {target with clock := target.clock + clock} targetBody bodyResult targetBodyExecution
          continuationGuard.1 recursiveClock
      have inputEq : {{target with clock := target.clock + clock} with
          clock := (target.clock + clock) + recursiveClock} =
          {target with clock := target.clock + (clock + recursiveClock)} := by
        simp only [Nat.add_assoc]
      rw [inputEq] at extendedBody stable
      have reentryEq : decClock {targetBody with clock := targetBody.clock + recursiveClock} =
          {decClock targetBody with clock := (decClock targetBody).clock + recursiveClock} := by
        simp only [decClock]
        congr 1
        omega
      refine ⟨clock + recursiveClock, targetPost, finalSpace, postRelation, ?_, guard, ?_⟩
      · rw [evaluateLoopUnclamped, extendedBody]
        simp only [continuing, if_true]
        rw [if_neg (show targetBody.clock + recursiveClock ≠ 0 by omega), reentryEq]
        exact targetExecution
      · conv_lhs => rw [stackExecutionCost]
        conv_rhs => rw [stackExecutionCost]
        simp only [StackSemEvaluateClock.fixClockEvaluate]
        simp only [StackSemEvaluateClock.fixClockEvaluate, extendedBody, bodyExecution,
          continuing, samePrice]
        simp only [show targetBody.clock + recursiveClock ≠ 0 by omega, zero,
          bne_iff_ne, ne_eq, not_false_eq_true, Bool.true_and, if_true]
        rw [stable, reentryEq]
        exact Nat.add_le_add (Nat.add_le_add_left bodyCost _) recursiveCost
  · have exit : contLoop bodyResult = false := by cases h : contLoop bodyResult <;> simp_all
    simp only [exit, Bool.false_eq_true, if_false] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    refine ⟨clock, targetBody, stackSpace, bodyRelation, ?_, ?_, ?_⟩
    · rw [evaluateLoopUnclamped, targetBodyExecution]
      simp only [exit, Bool.false_eq_true, if_false]
    · intro guard
      exact bodyGuard (exitLoopGuard bodyResult guard)
    · conv_lhs => rw [stackExecutionCost]
      conv_rhs => rw [stackExecutionCost]
      simp only [StackSemEvaluateClock.fixClockEvaluate]
      simp only [StackSemEvaluateClock.fixClockEvaluate, targetBodyExecution, bodyExecution,
        exit, Bool.false_and, Bool.false_eq_true, if_false, Nat.add_zero, samePrice]
      exact Nat.add_le_add_left bodyCost _

#print axioms executed_loop
end InitECandidate.Runtime.StackRawCall
