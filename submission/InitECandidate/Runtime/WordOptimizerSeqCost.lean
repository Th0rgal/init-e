import InitECandidate.Runtime.WordOptimizerPrice
import Flapjack.Compiler.Backend.WordUnreach.Proofs

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- Reassociating a sequence preserves its actual executed cost, including
early exits. Structural Seq nodes carry no optimizer price. -/
theorem optimizer_seq_assoc_cost_eq {C F : Type}
    (first second third : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (.seq (.seq first second) third) source =
      wordExecutionCost wordOptimizerLocalPrice (.seq first (.seq second third)) source := by
  simp only [wordExecutionCost_seq, wordOptimizerLocalPrice,
    WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  rw [evaluate, fix_clock_evaluate]
  rcases actual : evaluate first source with ⟨result, middle⟩
  cases result with
  | some outcome => simp only [actual, Nat.add_zero]
  | none =>
    simp only [actual]
    rcases next : evaluate second middle with ⟨result, post⟩
    cases result <;> simp only [next, Nat.add_zero, Nat.add_assoc]

theorem optimizer_move_nonerror_normal {C F : Type}
    (priority : Nat) (pairs : List (Nat × Nat)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.move priority pairs) source).1 ≠ some .error) :
    (evaluate (.move priority pairs) source).1 = none := by
  rw [WordUnreach.evaluateMove] at safe ⊢
  split
  · split <;> simp_all
  · simp_all

/-- A merged move pays no more than the two reached original moves. Unlike
a node-count argument, this compares the executed Word counters directly. -/
theorem optimizer_merged_move_cost_le {C F : Type}
    (firstPriority secondPriority mergedPriority : Nat)
    (first second : List (Nat × Nat)) (source : WordSemStateFiniteExact 64 C F)
    (normal : (evaluate (.move firstPriority first) source).1 = none) :
    wordExecutionCost wordOptimizerLocalPrice
      (.move mergedPriority (WordUnreach.mergeMoves first second)) source ≤
    wordExecutionCost wordOptimizerLocalPrice
      (.seq (.move firstPriority first) (.move secondPriority second)) source := by
  rcases actual : evaluate (.move firstPriority first) source with ⟨result, middle⟩
  have resultNone : result = none := by simpa only [actual] using normal
  subst resultNone
  have bound := mergeMoves_length_le first second
  simp only [wordExecutionCost_seq, actual, wordExecutionCost, wordOptimizerLocalPrice,
    WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  simpa only [Nat.mul_add] using Nat.mul_le_mul_left 24 bound

#print axioms optimizer_seq_assoc_cost_eq
#print axioms optimizer_move_nonerror_normal
#print axioms optimizer_merged_move_cost_le
end InitECandidate.Runtime.FineCost
