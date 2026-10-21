import InitECandidate.Runtime.WordFunctionPermuteGlobalCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- Cost-aware permutation stitching. This chooses a new input permutation
for a requested final permutation, preserving the actual result, every other
post-state field and executed cost. It does not assert equality for arbitrary
independently chosen input permutations. -/
def PermuteCostGoal {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) : Prop :=
  ∀ finalPermutation : Nat → Nat → Nat,
    (evaluate program source).1 ≠ some .error →
    ∃ initialPermutation,
      evaluate program {source with permute := initialPermutation} =
        ((evaluate program source).1, {(evaluate program source).2 with permute := finalPermutation}) ∧
      wordExecutionCost (fun p _ => price p) program {source with permute := initialPermutation} =
        wordExecutionCost (fun p _ => price p) program source

/-- Uniform-price specialization of the function-indexed whole-program
permutation theorem. This preserves the original public interface without
maintaining a second recursive proof of the same evaluator cases. -/
theorem word_permute_executed_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) :
    PermuteCostGoal price program source := by
  intro finalPermutation safe
  obtain ⟨initialPermutation,run,cost⟩ := word_function_permute_executed_cost
    (fun _ => price) 0 program source finalPermutation safe
  refine ⟨initialPermutation,run,?_⟩
  simpa only [wordFunctionExecutionCost_uniform] using cost

#print axioms word_permute_executed_cost
end InitECandidate.Runtime.FineCost
