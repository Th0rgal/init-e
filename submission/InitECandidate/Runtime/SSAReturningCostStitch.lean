import InitECandidate.Runtime.SSACallPermutationCost
import InitECandidate.Runtime.WordStackValueGlobalCost
import InitECandidate.Runtime.SSAQuantitativeCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Result/frame/locals and executed-work comparison share one outcome.
Source errors retain the original SSA exemption. This packages composition;
it does not posit a run or budget for a compiler output. -/
def SSAQuantitativeOutcome {C F : Type} (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F)
    (sourceWork targetWork : Nat) : Prop :=
  source.1 = some .error ∨ source.1 = target.1 ∧
    Flapjack.WordAlloc.wordStateEqRel source.2 target.2 ∧
    SSAResultLocals next map tables source.2.locals target.2.locals source.1 ∧ targetWork ≤ sourceWork

/-- Callee and selected-continuation cost composition. The actual callee
entries differ only in saved stack values. The continuation theorem chooses
an ending scheduler; cost-aware stitching chooses the callee input scheduler
while preserving its original work. Static caller overhead pays the exact
emitted continuation prefix. No recursive callee compiler IH is needed. -/
theorem ssa_returning_cost_stitch {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (callee : WordLangProgHOL (BitVec 64))
    (sourceEntry targetEntry : WordSemStateFiniteExact 64 C F)
    (entry : {sourceEntry with stack := targetEntry.stack} = targetEntry)
    (values : WordSemStackEq.sValEq sourceEntry.stack targetEntry.stack)
    (prices : ∀ p, TP p ≤ SP p)
    (map : Spt Nat) (next : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (sourceTail : (Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F) →
      Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F)
    (targetFinal : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F)
    (sourceRemainder : (Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F) → Nat)
    (sourceHead targetHead remainderPrefix targetRemainder : Nat)
    (overhead : targetHead + remainderPrefix ≤ sourceHead)
    (errorTail : ∀ post, (sourceTail (some .error, post)).1 = some .error)
    (continuation : ∃ finalPermutation,
      let sourceBody := ((evaluate callee sourceEntry).1,
        {(evaluate callee sourceEntry).2 with permute := finalPermutation})
      SSAQuantitativeOutcome map next tables (sourceTail sourceBody) targetFinal
        (remainderPrefix + sourceRemainder sourceBody) targetRemainder) :
    ∃ suffix,
      let sourceBody := evaluate callee {sourceEntry with permute := suffix}
      SSAQuantitativeOutcome map next tables (sourceTail sourceBody) targetFinal
        (sourceHead + wordExecutionCost (fun p _ => SP p) callee {sourceEntry with permute := suffix} +
          sourceRemainder sourceBody)
        (targetHead + wordExecutionCost (fun p _ => TP p) callee targetEntry + targetRemainder) := by
  let Q := fun result => SSAQuantitativeOutcome map next tables (sourceTail result) targetFinal
    (sourceHead + wordExecutionCost (fun p _ => SP p) callee sourceEntry + sourceRemainder result)
    (targetHead + wordExecutionCost (fun p _ => TP p) callee targetEntry + targetRemainder)
  have errorQ : ∀ post, evaluate callee sourceEntry = (some .error, post) → Q (some .error, post) := by
    intro post _
    exact Or.inl (errorTail post)
  have outcome : ∃ permutation, Q ((evaluate callee sourceEntry).1,
      {(evaluate callee sourceEntry).2 with permute := permutation}) := by
    obtain ⟨permutation, post⟩ := continuation
    refine ⟨permutation, ?_⟩
    dsimp only at post ⊢
    by_cases bad : (evaluate callee sourceEntry).1 = some .error
    · change SSAQuantitativeOutcome _ _ _ _ _ _ _
      left
      rw [bad]
      exact errorTail _
    · have invariant := word_stack_value_executed_cost SP callee sourceEntry bad targetEntry.stack values
      rw [entry] at invariant
      have mono := wordExecutionCost_mono (fun p (_ : WordSemStateFiniteExact 64 C F) => TP p)
        (fun p _ => SP p) (fun p _ => prices p) callee targetEntry
      have calleeCost := mono.trans (Nat.le_of_eq invariant)
      rcases post with error | ⟨same, frame, locals, restCost⟩
      · exact Or.inl error
      · refine Or.inr ⟨same, frame, locals, ?_⟩
        omega
  obtain ⟨suffix, post, cost⟩ := ssa_permute_predicate_cost SP callee sourceEntry Q errorQ outcome
  refine ⟨suffix, ?_⟩
  dsimp only [Q] at post
  rw [cost]
  exact post

#print axioms ssa_returning_cost_stitch
end InitECandidate.Runtime.FineCost
