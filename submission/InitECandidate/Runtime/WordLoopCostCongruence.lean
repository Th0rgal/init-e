import InitECandidate.Runtime.WordUnreachSimpCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- Replacing a loop body by a semantically equivalent cheaper body bounds
the whole actual loop. Recursion follows the actual remaining clock and the
body's resulting state, not an assumed equality of iteration counts. -/
theorem optimizer_loop_body_cost_le {C F : Type}
    (names exits : WordLangNumSetHOL) (body replacement : WordLangProgHOL (BitVec 64))
    (same : ∀ source : WordSemStateFiniteExact 64 C F,
      (evaluate body source).1 ≠ some .error → evaluate replacement source = evaluate body source)
    (cheaper : ∀ source : WordSemStateFiniteExact 64 C F,
      (evaluate body source).1 ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice replacement source ≤
        wordExecutionCost wordOptimizerLocalPrice body source)
    (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.loop names body exits) source).1 ≠ some .error) :
    wordExecutionCost wordOptimizerLocalPrice (.loop names replacement exits) source ≤
      wordExecutionCost wordOptimizerLocalPrice (.loop names body exits) source := by
  rw [wordExecutionCost, wordExecutionCost]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget]
  cases cut : cutState (names, .ln) source with
  | none => simp only [cut, Nat.le_refl]
  | some cutSource =>
    rcases actual : evaluate body cutSource with ⟨result, middle⟩
    have bodySafe : (evaluate body cutSource).1 ≠ some .error := by
      intro bad
      have error : result = some .error := by simpa only [actual] using bad
      rw [evaluate, cut] at safe
      dsimp only at safe
      rw [fix_clock_evaluate, actual, error] at safe
      simpa [wordSemContLoop, wordSemExitLoop] using safe
    have targetRun := (same cutSource bodySafe).trans actual
    have bodyCost := cheaper cutSource bodySafe
    simp only [cut, fix_clock_evaluate, actual, targetRun]
    have fixed : fixClock cutSource (result, middle) = (result, middle) := by
      rw [← actual, fix_clock_evaluate]
    rw [fixed]
    by_cases continuing : wordSemContLoop result = true
    · simp only [continuing, if_true]
      by_cases zero : middle.clock = 0
      · simp only [zero, if_true, Nat.add_zero]
        exact Nat.add_le_add_left bodyCost 2
      · simp only [zero, if_false, wordSemSTOP]
        have nextSafe : (evaluate (.loop names body exits) (decClock middle)).1 ≠ some .error := by
          rw [evaluate, cut] at safe
          dsimp only at safe
          rw [fix_clock_evaluate, actual] at safe
          simpa [continuing, zero, wordSemSTOP] using safe
        have clock := evaluate_clock body cutSource result middle actual
        have cutClock := cutState_clock_termdep (names, .ln) source cutSource cut
        exact Nat.add_le_add (Nat.add_le_add_left bodyCost 2)
          (optimizer_loop_body_cost_le names exits body replacement same cheaper (decClock middle) nextSafe)
    · simp only [continuing, if_false, Nat.add_zero]
      exact Nat.add_le_add_left bodyCost 2
termination_by source.clock
decreasing_by simp only [decClock]; omega

#print axioms optimizer_loop_body_cost_le
end InitECandidate.Runtime.FineCost
