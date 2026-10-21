import InitECandidate.Runtime.WordOptimizerSeqCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- A non-error sequence cannot have executed an erroring prefix. -/
theorem optimizer_seq_prefix_safe {C F : Type}
    (first second : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.seq first second) source).1 ≠ some .error) :
    (evaluate first source).1 ≠ some .error := by
  intro bad
  rcases actual : evaluate first source with ⟨result, middle⟩
  have error : result = some .error := by simpa only [actual] using bad
  rw [evaluate, fix_clock_evaluate, actual, error] at safe
  exact safe rfl

/-- Replacing an actual prefix by an equivalent cheaper prefix preserves the
work bound for its reached suffix, including all terminal prefix outcomes. -/
theorem optimizer_seq_prefix_cost_le {C F : Type}
    (first replacement suffix : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (sameRun : evaluate replacement source = evaluate first source)
    (cheaper : wordExecutionCost wordOptimizerLocalPrice replacement source ≤
      wordExecutionCost wordOptimizerLocalPrice first source) :
    wordExecutionCost wordOptimizerLocalPrice (.seq replacement suffix) source ≤
      wordExecutionCost wordOptimizerLocalPrice (.seq first suffix) source := by
  rw [wordExecutionCost_seq, wordExecutionCost_seq, sameRun]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  exact Nat.add_le_add_right cheaper _

/-- Merge two actual move executions before an arbitrary suffix. The prefix
run is constructed by the pinned merge theorem, and its work comes from the
input-pair bound; the same suffix state is therefore justified semantically. -/
theorem optimizer_merge_moves_suffix_cost_le {C F : Type}
    (firstPriority secondPriority mergedPriority : Nat)
    (first second : List (Nat × Nat)) (suffix : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.seq (.move firstPriority first) (.move secondPriority second)) source).1 ≠
      some .error) :
    wordExecutionCost wordOptimizerLocalPrice
      (.seq (.move mergedPriority (WordUnreach.mergeMoves first second)) suffix) source ≤
    wordExecutionCost wordOptimizerLocalPrice
      (.seq (.move firstPriority first) (.seq (.move secondPriority second) suffix)) source := by
  have firstSafe := optimizer_seq_prefix_safe (.move firstPriority first) (.move secondPriority second) source safe
  have normal := optimizer_move_nonerror_normal firstPriority first source firstSafe
  have cheaper := optimizer_merged_move_cost_le firstPriority secondPriority mergedPriority first second source normal
  rcases actual : evaluate (.seq (.move firstPriority first) (.move secondPriority second)) source with
    ⟨result, middle⟩
  have notError : result ≠ some .error := by simpa only [actual] using safe
  have sameRun := WordUnreach.mergeMovesSkip firstPriority secondPriority mergedPriority
    first second source result middle ⟨actual, notError⟩
  rw [← optimizer_seq_assoc_cost_eq]
  exact optimizer_seq_prefix_cost_le _ _ suffix source (sameRun.trans actual.symm) cheaper

#print axioms optimizer_seq_prefix_safe
#print axioms optimizer_seq_prefix_cost_le
#print axioms optimizer_merge_moves_suffix_cost_le
end InitECandidate.Runtime.FineCost
