import InitECandidate.Runtime.WordStackValueControlCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
open Flapjack.WordSemStackEq
set_option maxHeartbeats 4000000

/-- Cut only the locals; replacing the saved stack commutes with the cut. -/
theorem cutState_stack_only {C F : Type} (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact 64 C F) (stack : List (WordSemStackFrame 64)) :
    cutState names {source with stack := stack} =
      (cutState names source).map (fun post => {post with stack := stack}) := by
  unfold cutState
  dsimp only
  split <;> rfl

/-- Actual loop work is unchanged by renaming saved stack keys while keeping
frame values. The body and recursive hypotheses are at the reached states;
this is the loop constructor of the global quantitative stack-swap proof. -/
theorem stack_value_cost_loop {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (inner : ∀ entry, cutState (names, .ln) source = some entry → StackValueCostGoal price body entry)
    (next : ∀ entry result post, cutState (names, .ln) source = some entry →
      evaluate body entry = (result, post) → wordSemContLoop result = true → post.clock ≠ 0 →
      StackValueCostGoal price (.loop names body exits) (decClock post)) :
    StackValueCostGoal price (.loop names body exits) source := by
  intro safe stack related
  rcases cut : cutState (names, .ln) source with _ | entry
  · rw [evaluate, cut] at safe
    exact (safe rfl).elim
  rcases actual : evaluate body entry with ⟨result, post⟩
  have bodySafe : (evaluate body entry).1 ≠ some .error := by
    intro bad
    have error : result = some .error := by simpa only [actual] using bad
    rw [evaluate, cut] at safe
    dsimp only at safe
    rw [fix_clock_evaluate, actual, error] at safe
    simpa [wordSemContLoop, wordSemExitLoop] using safe
  obtain ⟨locals, entryEq⟩ := cutStateConst (names, .ln) source entry cut
  have entryStack : entry.stack = source.stack := by rw [entryEq]
  have entryRelated : sValEq entry.stack stack := entryStack.symm ▸ related
  have targetCut : cutState (names, .ln) {source with stack := stack} =
      some {entry with stack := stack} := by
    rw [cutState_stack_only, cut]
    rfl
  have bodyCost := inner entry cut bodySafe stack entryRelated
  have sourceCost := pure_loop_cost_run price names exits body source entry post result cut actual
  by_cases continuing : wordSemContLoop result = true
  · obtain ⟨afterStack, swapped, values⟩ := stack_value_continuing body entry post result stack actual entryRelated continuing
    have targetCost := pure_loop_cost_run price names exits body {source with stack := stack}
      {entry with stack := stack} {post with stack := afterStack} result targetCut swapped
    rw [targetCost, sourceCost, bodyCost]
    simp only [continuing, if_true]
    by_cases zero : post.clock = 0
    · simp only [zero, if_true]
    · have sourceEq := WordToWord.evaluate_loop_run names exits body source entry cut result post actual
      have nextSafe : (evaluate (.loop names body exits) (decClock post)).1 ≠ some .error := by
        rw [sourceEq] at safe
        simpa only [continuing, if_true, zero, if_false, wordSemSTOP] using safe
      have cost := next entry result post cut actual continuing zero nextSafe afterStack values
      have decrement : decClock {post with stack := afterStack} = {(decClock post) with stack := afterStack} := rfl
      simp only [zero, if_false]
      rw [decrement]
      exact congrArg
        (fun n => price (.loop names body exits) + wordExecutionCost (fun p _ => price p) body entry + n) cost
  · have same := stack_value_result body entry stack entryRelated bodySafe
    rcases swapped : evaluate body {entry with stack := stack} with ⟨targetResult, targetPost⟩
    have resultEq : targetResult = result := by simpa only [actual, swapped] using same
    subst targetResult
    have targetCost := pure_loop_cost_run price names exits body {source with stack := stack}
      {entry with stack := stack} targetPost result targetCut swapped
    rw [targetCost, sourceCost, bodyCost]
    simp only [continuing, Bool.false_eq_true, if_false]

#print axioms cutState_stack_only
#print axioms stack_value_cost_loop
end InitECandidate.Runtime.FineCost
