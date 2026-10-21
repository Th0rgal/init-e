import InitECandidate.Runtime.RawCallExecutedLoop
import InitECandidate.Runtime.RawCallRefinedLocalPrice

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase
open InitECandidate.Runtime.StackToLab

/-- Successful optimized sequence from the actual second-program quantitative
IH. The target call, its recursive callee cost and all terminal outcomes are
constructed by that IH. Only its known entry shape is supplied separately. -/
theorem executed_optimized_seq_success {F : Type} (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) (targetBody : HolProg 64) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (entry : sptLookup dest target.code = some (.seq (.stackAlloc allocated) targetBody))
    (enabled : source.useStack = true) (nonzero : source.clock ≠ 0)
    (releaseSafe : source.stackSpace + released ≤ source.stack.length)
    (space : allocated ≤ source.stackSpace + released)
    (positive : 0 < released) (releaseBound : released ≤ 255) (allocationBound : allocated ≤ 255)
    (secondIH : ∀ middle, StackSemEvaluate.evaluate (.stackFree released, source) = (none, middle) →
      ExecutedProgramIH (refinedRemovalLocalPrice 6 bounds) (.call none (.inl dest) none) middle)
    (hypothesis : StackSemEvaluate.evaluate
        (.seq (.stackFree released) (.call none (.inl dest) none), source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds)
      (optimizedSeq released allocated dest) info target post result
      (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
        (.seq (.stackFree released) (.call none (.inl dest) none)) source) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have originalRelation := relation
  have targetSpace : target.stackSpace = source.stackSpace := by
    obtain ⟨code, domain, targetEq, rest⟩ := relation
    subst target
    rfl
  have targetClock : target.clock = source.clock := LoopCase.stateRel_clock info source target relation
  have targetEnabled : target.useStack = true := by
    obtain ⟨code, domain, targetEq, rest⟩ := relation
    subst target
    exact enabled
  have targetBounds : target.stackSpace + released ≤ target.stack.length := by
    obtain ⟨code, domain, targetEq, rest⟩ := relation
    subst target
    exact releaseSafe
  have freeRun : StackSemEvaluate.evaluate (.stackFree released, source) =
      (none, {source with stackSpace := source.stackSpace + released}) := by
    simp [StackSemEvaluate.evaluate_stackFree, enabled, Nat.not_lt.mpr releaseSafe]
  rw [evaluateSeqUnclamped, freeRun] at execution
  have shiftedRelation := stateRel_setStackSpace info source target relation
    (source.stackSpace + released)
  obtain ⟨clock, targetPost, finalSpace, postRelation, targetRun, guard, cost⟩ :=
    secondIH _ freeRun info {target with stackSpace := source.stackSpace + released}
      post result ⟨execution, nonerror, shiftedRelation⟩
  have callInput : {{target with stackSpace := source.stackSpace + released} with
      clock := target.clock + clock} =
      {{target with clock := target.clock + clock} with
        stackSpace := target.stackSpace + released} := by rw [targetSpace]
  change StackSemEvaluate.evaluate (.call none (.inl dest) none,
    {{target with stackSpace := source.stackSpace + released} with clock := target.clock + clock}) =
    (result, {targetPost with stackSpace := finalSpace}) at targetRun
  rw [callInput] at targetRun
  have transport := successfulOptimization released allocated dest targetBody
    {target with clock := target.clock + clock} entry targetEnabled targetBounds
    (by simpa only [targetSpace] using space) (by simp only; rw [targetClock]; omega)
  have combinedInput : {{target with clock := target.clock + clock} with
      clock := (target.clock + clock) + (if released < allocated then 1 else 0)} =
      {target with clock := target.clock + (clock + (if released < allocated then 1 else 0))} := by
    simp only [Nat.add_assoc]
  rw [combinedInput] at transport
  refine ⟨clock + (if released < allocated then 1 else 0), targetPost, finalSpace,
    postRelation, transport.trans targetRun, guard, ?_⟩
  have optimizedBound := optimizedTail_executionCost_le bounds released allocated dest targetBody
    {target with clock := target.clock + clock} entry targetEnabled
    (by simp only; rw [targetClock]; omega) targetBounds
    (by simpa only [targetSpace] using space) positive releaseBound allocationBound
  rw [combinedInput] at optimizedBound
  have targetFreeRun : StackSemEvaluate.evaluate (.stackFree released,
      {target with clock := target.clock + clock}) =
      (none, {{target with clock := target.clock + clock} with stackSpace := target.stackSpace + released}) := by
    simp [StackSemEvaluate.evaluate_stackFree, targetEnabled, Nat.not_lt.mpr targetBounds]
  have targetSeqCost : stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
      (.seq (.stackFree released) (.call none (.inl dest) none))
      {target with clock := target.clock + clock} =
      refinedRemovalLocalPrice 6 bounds (.stackFree released) +
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
        (.call none (.inl dest) none)
        {{target with clock := target.clock + clock} with stackSpace := target.stackSpace + released} := by
    simp [stackExecutionCost_seq, targetFreeRun, stackExecutionCost,
      refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap]
  rw [targetSeqCost] at optimizedBound
  change stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
      (.call none (.inl dest) none)
      {{target with stackSpace := source.stackSpace + released} with clock := target.clock + clock} ≤ _ at cost
  rw [callInput] at cost
  have sourceSeqCost : stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
      (.seq (.stackFree released) (.call none (.inl dest) none)) source =
      refinedRemovalLocalPrice 6 bounds (.stackFree released) +
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
        (.call none (.inl dest) none) {source with stackSpace := source.stackSpace + released} := by
    simp [stackExecutionCost_seq, freeRun, stackExecutionCost,
      refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap]
  rw [sourceSeqCost]
  exact optimizedBound.trans (Nat.add_le_add_left cost _)

#print axioms executed_optimized_seq_success
end InitECandidate.Runtime.StackRawCall
