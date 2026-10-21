import InitECandidate.Runtime.WordPermuteLoopStitch
import InitECandidate.Runtime.WordStackValueControlCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Stitch the recursive loop witness without changing the measured body
work. The loop head pays the reached back-edge allowance; one-off setup is
outside this theorem and is not repeated by the recursive hypothesis. -/
theorem ssa_loop_recursive_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (names exits targetNames targetExits : Spt Unit)
    (body finalBody : WordLangProgHOL (BitVec 64))
    (source sourcePost sourceFinal target targetEntry targetPost targetFinal :
      WordSemStateFiniteExact 64 C F)
    (env : Spt (WordLocW 64)) (bodyResult finalResult : Option (WordSemResult 64))
    (recursivePermutation : Nat → Nat → Nat) (backedgeWork : Nat)
    (sourceCut : wordSemCutEnv (names, .ln) source.locals = some env)
    (targetCut : cutState (targetNames, .ln) target = some targetEntry)
    (sourceBody : evaluate body {source with locals := env} = (bodyResult, sourcePost))
    (targetBody : evaluate finalBody targetEntry = (bodyResult, targetPost))
    (notError : bodyResult ≠ some .error)
    (continuing : wordSemContLoop bodyResult = true)
    (sourceNonzero : sourcePost.clock ≠ 0) (targetNonzero : targetPost.clock ≠ 0)
    (sourceRecursive : evaluate (.loop names body exits)
      {(decClock sourcePost) with permute := recursivePermutation} = (finalResult, sourceFinal))
    (targetRecursive : evaluate (.loop targetNames finalBody targetExits)
      (decClock targetPost) = (finalResult, targetFinal))
    (bodyCost : wordExecutionCost (fun p _ => TP p) finalBody targetEntry ≤
      wordExecutionCost (fun p _ => SP p) body {source with locals := env} + backedgeWork)
    (recursiveCost : wordExecutionCost (fun p _ => TP p)
      (.loop targetNames finalBody targetExits) (decClock targetPost) ≤
      wordExecutionCost (fun p _ => SP p) (.loop names body exits)
        {(decClock sourcePost) with permute := recursivePermutation})
    (headCost : TP (.loop targetNames finalBody targetExits) + backedgeWork ≤
      SP (.loop names body exits)) :
    ∃ permutation,
      evaluate (.loop names body exits) {source with permute := permutation} =
        (finalResult, sourceFinal) ∧
      evaluate (.loop targetNames finalBody targetExits) target = (finalResult, targetFinal) ∧
      wordExecutionCost (fun p _ => TP p) (.loop targetNames finalBody targetExits) target ≤
        wordExecutionCost (fun p _ => SP p) (.loop names body exits)
          {source with permute := permutation} := by
  obtain ⟨permutation, sourceRun, sourceCost⟩ := stitch_recursive_loop_cost SP source sourcePost
    sourceFinal names exits body env bodyResult finalResult recursivePermutation sourceCut
    sourceBody notError continuing sourceNonzero sourceRecursive
  have targetRun := WordToWord.evaluate_loop_run targetNames targetExits finalBody target
    targetEntry targetCut bodyResult targetPost targetBody
  have targetCost := pure_loop_cost_run TP targetNames targetExits finalBody target targetEntry
    targetPost bodyResult targetCut targetBody
  refine ⟨permutation, sourceRun, ?_, ?_⟩
  · rw [targetRun]
    simpa only [continuing, if_true, targetNonzero, if_false, wordSemSTOP] using targetRecursive
  · rw [targetCost, sourceCost]
    simp only [continuing, if_true, targetNonzero, if_false]
    dsimp only at recursiveCost sourceCost
    omega

#print axioms ssa_loop_recursive_cost
end InitECandidate.Runtime.FineCost
