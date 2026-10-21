import InitECandidate.Runtime.RawCallExecutedTail

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase
open InitECandidate.Runtime.StackToLab

/-- Before callee execution, the direct-call counter is independent of the
callee body and all other code entries. This covers timeout and allocation
failure, retaining the real evaluator's short-circuit behavior. -/
theorem tailEntry_early_cost {F : Type} (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (entry : sptLookup dest source.code = some (.seq (.stackAlloc allocated) body))
    (enabled : source.useStack = true)
    (releaseSafe : source.stackSpace + released ≤ source.stack.length)
    (early : source.clock = 0 ∨ source.stackSpace + released < allocated) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
      (.seq (.stackFree released) (.call none (.inl dest) none)) source =
      refinedRemovalLocalPrice 6 bounds (.stackFree released) + 2 +
        (if source.clock = 0 then 0 else refinedRemovalLocalPrice 6 bounds (.stackAlloc allocated)) := by
  have freeRun : StackSemEvaluate.evaluate (.stackFree released, source) =
      (none, {source with stackSpace := source.stackSpace + released}) := by
    simp [StackSemEvaluate.evaluate_stackFree, enabled, Nat.not_lt.mpr releaseSafe]
  rw [stackExecutionCost_seq, freeRun]
  rcases early with zero | failure
  · simp [stackExecutionCost, zero, refinedRemovalLocalPrice, removalLocalPrice,
      nativePriceWithGap, callJumpWork]
  · by_cases zero : source.clock = 0
    · simp [stackExecutionCost, zero, refinedRemovalLocalPrice, removalLocalPrice,
        nativePriceWithGap, callJumpWork]
    · simp [stackExecutionCost, zero, findCode, entry,
        StackSemEvaluate.evaluate_stackAlloc, decClock, enabled, failure,
        fixClock, emptyEnv, refinedRemovalLocalPrice, removalLocalPrice,
        nativePriceWithGap, callJumpWork, Nat.add_assoc]

/-- Full optimized sequence, including invalid release states, timeouts,
allocation failure and successful callee entry. The frame lookup and code
relation derive the actual transformed callee declaration. -/
theorem executed_optimized_seq {F : Type} (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (frame : sptLookup dest info = some allocated)
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
  have originalHypothesis := hypothesis
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have originalRelation := relation
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  have targetSpace : target.stackSpace = source.stackSpace := by rw [targetEq]
  have targetClock : target.clock = source.clock := by rw [targetEq]
  have clockSelf : {target with clock := target.clock + 0} = target := by cases target; simp
  rw [evaluateSeqUnclamped, StackSemEvaluate.evaluate_stackFree] at execution
  by_cases enabled : source.useStack = true
  · simp only [enabled, Bool.not_true, Bool.false_eq_true, if_false] at execution
    by_cases badBounds : source.stack.length < source.stackSpace + released
    · simp only [badBounds, if_true, Prod.mk.injEq] at execution
      exact False.elim (nonerror execution.1.symm)
    · simp only [badBounds, if_false] at execution
      have releaseSafe : source.stackSpace + released ≤ source.stack.length := by omega
      have shiftedRelation := stateRel_setStackSpace info source target originalRelation
        (source.stackSpace + released)
      have targetEnabled : target.useStack = true := by simpa only [targetEq] using enabled
      have targetBounds : target.stackSpace + released ≤ target.stack.length := by
        simpa only [targetEq] using releaseSafe
      obtain ⟨body, sourceEntry⟩ := frames dest allocated frame
      obtain ⟨entryInfo, _, targetLookup⟩ := RawCallCase.rawCallEntry info source target originalRelation
        dest (.stackAlloc allocated) body sourceEntry
      have targetEntry : sptLookup dest target.code =
          some (.seq (.stackAlloc allocated) (comp entryInfo body)) := by
        simpa only [comp] using targetLookup
      replace execution : StackSemEvaluate.evaluate (.call none (.inl dest) none,
          {source with stackSpace := source.stackSpace + released}) = (result, post) := by
        simpa only [enabled] using execution
      rw [evaluateCallAlloc dest allocated body
        {source with stackSpace := source.stackSpace + released} sourceEntry] at execution
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        let targetPost := emptyEnv {target with stackSpace := source.stackSpace + released}
        refine ⟨0, targetPost,
          (if allocated < released then target.stackSpace + (released - allocated)
           else target.stackSpace), ?_, ?_, by simp, ?_⟩
        · simpa only [zero] using LoopCase.stateRel_emptyEnv info
            {source with stackSpace := source.stackSpace + released}
            {target with stackSpace := source.stackSpace + released} shiftedRelation
        · rw [clockSelf]
          simpa only [targetPost, emptyEnv] using
            zeroOptimization released allocated dest (comp entryInfo body) target targetEntry
              targetEnabled targetBounds (targetClock.trans zero)
        · rw [clockSelf]
          have localBound := optimizedTail_zero_executionCost_le bounds released allocated dest
            target targetEnabled (targetClock.trans zero) targetBounds positive releaseBound
          have sourceCost := tailEntry_early_cost bounds released allocated dest body source
            sourceEntry enabled releaseSafe (Or.inl zero)
          have targetCost := tailEntry_early_cost bounds released allocated dest (comp entryInfo body)
            target targetEntry targetEnabled targetBounds (Or.inl (targetClock.trans zero))
          rw [targetCost] at localBound
          rw [sourceCost]
          simpa only [targetClock] using localBound
      · simp only [zero, if_false,
          if_neg (show ¬ (!source.useStack) = true by simp [enabled])] at execution
        by_cases failure : source.stackSpace + released < allocated
        · simp only [failure, if_true, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          let targetPost := emptyEnv (decClock {target with stackSpace := source.stackSpace + released})
          refine ⟨0, targetPost, target.stackSpace,
            LoopCase.stateRel_emptyEnv info _ _
              (LoopCase.stateRel_decClock info _ _ shiftedRelation), ?_, by simp, ?_⟩
          · rw [clockSelf]
            simpa only [targetPost, emptyEnv, decClock] using
              failedOptimization released allocated dest target targetEnabled
                (by simpa only [targetSpace] using failure) (by simpa only [targetClock] using zero)
          · rw [clockSelf]
            have localBound := optimizedTail_failure_executionCost_le bounds released allocated dest
              (comp entryInfo body) target targetEntry targetEnabled
              (by simpa only [targetClock] using zero) targetBounds
              (by simpa only [targetSpace] using failure) positive releaseBound allocationBound
            have sourceCost := tailEntry_early_cost bounds released allocated dest body source
              sourceEntry enabled releaseSafe (Or.inr failure)
            have targetCost := tailEntry_early_cost bounds released allocated dest (comp entryInfo body)
              target targetEntry targetEnabled targetBounds
              (Or.inr (by simpa only [targetSpace] using failure))
            rw [targetCost] at localBound
            rw [sourceCost]
            simpa only [targetClock] using localBound
        · exact executed_optimized_seq_success bounds released allocated dest (comp entryInfo body)
            info source target post result targetEntry enabled zero releaseSafe
            (by omega) positive releaseBound allocationBound secondIH originalHypothesis
  · simp [enabled] at execution
    exact False.elim (nonerror execution.1.symm)

#print axioms tailEntry_early_cost
#print axioms executed_optimized_seq
end InitECandidate.Runtime.StackRawCall
