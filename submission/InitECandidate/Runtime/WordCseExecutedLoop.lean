import InitECandidate.Runtime.WordCseExecutedSeq

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- CSE loop cost follows the real cut state, the real body result and the
remaining-clock recursive iteration. The semantic body run comes from pinned
CSE correctness, so an unrelated target run cannot satisfy this contract. -/
theorem cse_loop_executed_cost_le {C F : Type}
    (data : WordCse.Knowledge) (names exits : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (flat : flatExpConventions body = true)
    (safe : ∀ cutSource, cutState (names, .ln) source = some cutSource →
      (evaluate body cutSource).1 ≠ some .error)
    (bodyBound : ∀ cutSource, cutState (names, .ln) source = some cutSource →
      wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse WordCse.emptyData body).2 cutSource ≤
        wordExecutionCost wordOptimizerLocalPrice body cutSource)
    (nextBound : ∀ cutSource result middle,
      cutState (names, .ln) source = some cutSource → evaluate body cutSource = (result, middle) →
      wordSemContLoop result = true → middle.clock ≠ 0 →
      wordExecutionCost wordOptimizerLocalPrice
        (WordCse.wordCse data (.loop names body exits)).2 (decClock middle) ≤
      wordExecutionCost wordOptimizerLocalPrice (.loop names body exits) (decClock middle)) :
    wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data (.loop names body exits)).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice (.loop names body exits) source := by
  rcases compiled : WordCse.wordCse WordCse.emptyData body with ⟨bodyData, body'⟩
  simp only [WordCse.wordCse, compiled] at bodyBound nextBound ⊢
  rw [wordExecutionCost, wordExecutionCost]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget]
  cases cut : cutState (names, .ln) source with
  | none => simp only [cut, Nat.le_refl]
  | some cutSource =>
    rcases actual : evaluate body cutSource with ⟨result, middle⟩
    have notError : result ≠ some .error := by simpa only [actual] using safe cutSource cut
    have targetRun := (WordCse.comp_correct body cutSource result middle
      WordCse.emptyData body' bodyData
      ⟨actual, flat, WordCse.dataInvEmpty cutSource, notError, compiled⟩).1
    simp only [cut, fix_clock_evaluate, actual, targetRun]
    have fixed : fixClock cutSource (result, middle) = (result, middle) := by
      rw [← actual, fix_clock_evaluate]
    rw [fixed]
    have bodyCost := bodyBound cutSource cut
    by_cases continuing : wordSemContLoop result = true
    · simp only [continuing, if_true]
      by_cases zero : middle.clock = 0
      · simp only [zero, if_true, Nat.add_zero]
        exact Nat.add_le_add_left bodyCost 2
      · simp only [zero, if_false, wordSemSTOP]
        exact Nat.add_le_add (Nat.add_le_add_left bodyCost 2)
          (nextBound cutSource result middle cut actual continuing zero)
    · simp only [continuing, if_false, Nat.add_zero]
      exact Nat.add_le_add_left bodyCost 2

#print axioms cse_loop_executed_cost_le

/-- MustTerminate runs the compiled body with exactly the source wrapper's
clock and term-depth update. Entering at zero term depth charges no body on
either side; no program-size multiplier is introduced. -/
theorem cse_mustTerminate_executed_cost_le {C F : Type}
    (data : WordCse.Knowledge) (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (bodyBound : source.termdep ≠ 0 →
      wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data body).2
        {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1} ≤
      wordExecutionCost wordOptimizerLocalPrice body
        {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}) :
    wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data (.mustTerminate body)).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice (.mustTerminate body) source := by
  simp only [WordCse.wordCse]
  rw [wordExecutionCost, wordExecutionCost]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  by_cases zero : source.termdep = 0
  · simp only [zero, dif_pos, Nat.le_refl]
  · simpa [zero] using bodyBound zero

/-- CSE leaves Call and its embedded continuations literally unchanged. Its
local transformation therefore preserves the complete actual call cost,
including the actual callee fetched from the current code table. Mapping an
entire code table still requires a separate global relation. -/
theorem cse_call_executed_cost_eq {C F : Type}
    (data : WordCse.Knowledge)
    (returns : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (destination : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice
      (WordCse.wordCse data (.call returns destination arguments handler)).2 source =
      wordExecutionCost wordOptimizerLocalPrice (.call returns destination arguments handler) source := by
  rfl

#print axioms cse_mustTerminate_executed_cost_le
#print axioms cse_call_executed_cost_eq
end InitECandidate.Runtime.FineCost
