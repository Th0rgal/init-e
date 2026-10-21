import InitECandidate.Runtime.WordPermuteLoopCost
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Call

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- A tail call stitches the actual selected callee without consuming a
permutation for a saved caller frame. -/
theorem permute_cost_tail {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (destination : Option Nat) (arguments : List Nat) (source : WordSemStateFiniteExact 64 C F)
    (inner : ∀ xs actualArguments body size,
      getVars arguments source = some xs →
      wordSemFindCode destination xs source.code source.stackSize = some (actualArguments, body, size) →
      source.clock ≠ 0 → PermuteCostGoal price body (callEnv actualArguments size (decClock source))) :
    PermuteCostGoal price (.call none destination arguments none) source := by
  intro finalPermutation safe
  rw [WordToWord.evaluate_call_eq] at safe
  rcases get : getVars arguments source with _ | xs
  · simp only [get] at safe
    exact (safe rfl).elim
  simp only [get] at safe
  by_cases bad : wordSemBadDestArgs destination arguments = true
  · simp only [bad, if_true] at safe
    exact (safe rfl).elim
  have good : wordSemBadDestArgs destination arguments = false := by simpa using bad
  simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc] at safe
  rcases found : wordSemFindCode destination xs source.code source.stackSize with
    _ | ⟨actualArguments, body, size⟩
  · simp only [found] at safe
    exact (safe rfl).elim
  simp only [found] at safe
  have targetGet : ∀ q : Nat → Nat → Nat,
      getVars arguments {source with permute := q} = some xs := by
    intro q
    rw [getVars_withPermute, get]
  by_cases zero : source.clock = 0
  · refine ⟨finalPermutation, ?_, ?_⟩
    · rw [WordToWord.evaluate_call_eq, WordToWord.evaluate_call_eq, targetGet, get]
      simp [good, wordSemAddRetLoc, found, zero, flushState]
    · conv_lhs => rw [wordExecutionCost]
      conv_rhs => rw [wordExecutionCost]
      simp only [getVars_withPermute, get]
      simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found, zero, dite_true]
  simp only [zero, if_false] at safe
  let entry := callEnv actualArguments size (decClock source)
  rcases actual : evaluate body entry with ⟨result, post⟩
  have entryRun : evaluate body (callEnv actualArguments size (decClock source)) = (result, post) := actual
  rw [entryRun] at safe
  have resultSafe : (evaluate body entry).1 ≠ some .error := by
    rw [actual]
    change result ≠ some .error
    intro badResult
    subst result
    simp [wordSemBadFunReturn] at safe
  obtain ⟨initialPermutation, bodyRun, bodyCost⟩ :=
    inner xs actualArguments body size get found zero finalPermutation resultSafe
  rw [entryRun] at bodyRun
  have targetEntry : callEnv actualArguments size (decClock {source with permute := initialPermutation}) =
      {entry with permute := initialPermutation} := rfl
  refine ⟨initialPermutation, ?_, ?_⟩
  · rw [WordToWord.evaluate_call_eq, WordToWord.evaluate_call_eq, targetGet, get]
    simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found, zero]
    rw [targetEntry, bodyRun, entryRun]
    split <;> rfl
  · conv_lhs => rw [wordExecutionCost]
    conv_rhs => rw [wordExecutionCost]
    simp only [getVars_withPermute, get, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found, zero, dite_false]
    rw [targetEntry, bodyCost]

#print axioms permute_cost_tail
end InitECandidate.Runtime.FineCost
