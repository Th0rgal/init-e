import InitECandidate.Runtime.WordPermuteGlobalCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- Quantitative counterpart of the pinned SSA loop's private
`stitchRecursiveRun`: choose the body permutation that ends at the recursive
witness, preserving its actual work. The outer cost is the sum of exactly
that body run and that recursive run, with one loop-head charge. -/
theorem stitch_recursive_loop_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat)
    (source after final : WordSemStateFiniteExact 64 C F)
    (names exits : Spt Unit) (body : WordLangProgHOL (BitVec 64))
    (env : Spt (WordLocW 64)) (bodyResult finalResult : Option (WordSemResult 64))
    (recursivePermutation : Nat → Nat → Nat)
    (cut : wordSemCutEnv (names, .ln) source.locals = some env)
    (bodyRun : evaluate body {source with locals := env} = (bodyResult, after))
    (notError : bodyResult ≠ some .error)
    (continuing : wordSemContLoop bodyResult = true) (nonzero : after.clock ≠ 0)
    (recursiveRun : evaluate (.loop names body exits)
      {(decClock after) with permute := recursivePermutation} = (finalResult, final)) :
    ∃ permutation,
      evaluate (.loop names body exits) {source with permute := permutation} = (finalResult, final) ∧
      wordExecutionCost (fun p _ => price p) (.loop names body exits) {source with permute := permutation} =
        price (.loop names body exits) + wordExecutionCost (fun p _ => price p) body {source with locals := env} +
          wordExecutionCost (fun p _ => price p) (.loop names body exits)
            {(decClock after) with permute := recursivePermutation} := by
  obtain ⟨permutation, swappedRun, swappedCost⟩ :=
    word_permute_executed_cost price body {source with locals := env} recursivePermutation
      (by simpa only [bodyRun] using notError)
  rw [bodyRun] at swappedRun
  have stateCut : cutState (names, .ln) {source with permute := permutation} =
      some {source with locals := env, permute := permutation} := by
    unfold cutState
    dsimp only
    rw [cut]
  refine ⟨permutation, ?_, ?_⟩
  · have whole := WordToWord.evaluate_loop_run names exits body {source with permute := permutation}
      {source with locals := env, permute := permutation} stateCut bodyResult
      {after with permute := recursivePermutation} swappedRun
    rw [whole]
    simp only [continuing, if_true, nonzero, if_false, wordSemSTOP]
    exact recursiveRun
  · rw [wordExecutionCost, stateCut]
    dsimp only
    rw [fix_clock_evaluate, swappedRun]
    simp only [continuing, if_true, nonzero, dif_neg, dite_false, dite_true, wordSemSTOP]
    rw [swappedCost]
    rfl

#print axioms stitch_recursive_loop_cost
end InitECandidate.Runtime.FineCost
