import InitECandidate.Runtime.WordCseLocalCost
import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-- Quantitative CSE sequencing uses the actual transformed prefix execution
and its re-established knowledge invariant. No target execution or target
cost bound is assumed beyond the two recursive source-sized obligations. -/
theorem cse_seq_executed_cost_le {C F : Type}
    (data : WordCse.Knowledge) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (flat : flatExpConventions first = true) (valid : WordCse.dataInv data source)
    (notError : (evaluate first source).1 ≠ some .error)
    (firstBound : wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data first).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice first source)
    (secondBound : ∀ middle, evaluate first source = (none, middle) →
      WordCse.dataInv (WordCse.wordCse data first).1 middle →
      wordExecutionCost wordOptimizerLocalPrice
        (WordCse.wordCse (WordCse.wordCse data first).1 second).2 middle ≤
      wordExecutionCost wordOptimizerLocalPrice second middle) :
    wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data (.seq first second)).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice (.seq first second) source := by
  rcases compiledFirst : WordCse.wordCse data first with ⟨nextData, first'⟩
  rcases compiledSecond : WordCse.wordCse nextData second with ⟨finalData, second'⟩
  rw [compiledFirst] at firstBound secondBound
  simp only [Prod.fst, Prod.snd, compiledSecond] at firstBound secondBound
  rcases actual : evaluate first source with ⟨result, middle⟩
  have safe : result ≠ some .error := by simpa only [actual] using notError
  obtain ⟨targetRun, nextValid⟩ := WordCse.comp_correct first source result middle
    data first' nextData ⟨actual, flat, valid, safe, compiledFirst⟩
  simp only [WordCse.wordCse, compiledFirst, compiledSecond]
  rw [wordExecutionCost_seq, wordExecutionCost_seq, actual, targetRun]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  cases result with
  | none => exact Nat.add_le_add firstBound (secondBound middle actual (nextValid rfl))
  | some outcome => exact Nat.add_le_add_right firstBound 0

#print axioms cse_seq_executed_cost_le

/-- Conditional work follows only the actually selected arm. CSE changes
neither the guard registers nor its comparison, so no branch maximum or
whole-program factor is introduced. -/
theorem cse_if_executed_cost_le {C F : Type}
    (data : WordCse.Knowledge) (cmp : Compiler.Encoders.Asm.HolCmp)
    (register : Nat) (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (yes : wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data first).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice first source)
    (no : wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data second).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice second source) :
    wordExecutionCost wordOptimizerLocalPrice
      (WordCse.wordCse data (.ite cmp register operand first second)).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice (.ite cmp register operand first second) source := by
  simp only [WordCse.wordCse]
  rw [wordExecutionCost, wordExecutionCost]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget]
  cases left : getVar register source with
  | none => simp only [left, Nat.le_refl]
  | some x =>
    cases right : getVarImm operand source with
    | none => simp only [left, right, Nat.le_refl]
    | some y =>
      cases compared : wordSemWordCmp cmp x y with
      | none => simp only [left, right, compared, Nat.le_refl]
      | some b =>
        cases b
        · simpa only [left, right, compared] using Nat.add_le_add_left no 23
        · simpa only [left, right, compared] using Nat.add_le_add_left yes 23

#print axioms cse_if_executed_cost_le
end InitECandidate.Runtime.FineCost
