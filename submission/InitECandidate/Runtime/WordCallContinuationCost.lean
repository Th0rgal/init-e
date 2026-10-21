import InitECandidate.Runtime.WordCallExecutionCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- A returning call with unchanged code/callee pays the actual selected
continuation's work. Only non-error continuation runs need the recursive
bound, since the source whole-call premise excludes an error there. -/
theorem optimizer_returning_none_continuation_cost_le {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (continuation replacement : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (destination : Option Nat) (arguments : List Nat) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.call (some (values, names, continuation, l1, l2))
      destination arguments none) source).1 ≠ some .error)
    (next : ∀ post : WordSemStateFiniteExact 64 C F,
      (evaluate continuation post).1 ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice replacement post ≤
        wordExecutionCost wordOptimizerLocalPrice continuation post) :
    wordExecutionCost wordOptimizerLocalPrice
      (.call (some (values, names, replacement, l1, l2)) destination arguments none) source ≤
    wordExecutionCost wordOptimizerLocalPrice
      (.call (some (values, names, continuation, l1, l2)) destination arguments none) source := by
  have retLoc (xs : List (WordLocW 64)) :
      wordSemAddRetLoc (some (values, names, replacement, l1, l2)) xs =
      wordSemAddRetLoc (some (values, names, continuation, l1, l2)) xs := rfl
  rw [evaluate] at safe
  rcases hg : getVars arguments source with _ | xs
  · simp only [hg] at safe
    exact (safe rfl).elim
  simp only [hg] at safe
  by_cases bad : wordSemBadDestArgs destination arguments = true
  · simp only [bad, if_true] at safe
    exact (safe rfl).elim
  have notBad : wordSemBadDestArgs destination arguments = false := by simpa using bad
  simp only [bad, Bool.false_eq_true, if_false, wordSemAddRetLoc] at safe
  rcases found : wordSemFindCode destination (.loc l1 l2 :: xs) source.code source.stackSize with
    _ | ⟨actualArgs, body, size⟩
  · simp only [found] at safe
    exact (safe rfl).elim
  simp only [found] at safe
  by_cases badNames : sptDomainEmpty names.1 ∨ ¬ values.Nodup
  · simp only [badNames, if_true] at safe
    exact (safe rfl).elim
  simp only [badNames, if_false] at safe
  rcases cut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [cut] at safe
    exact (safe rfl).elim
  simp only [cut] at safe
  by_cases zero : source.clock = 0
  · rw [wordExecutionCost, wordExecutionCost]
    simp [hg, notBad, wordSemAddRetLoc, found, badNames, cut, zero,
      wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
  simp only [zero, dif_neg] at safe
  rcases actual : evaluate body (callEnv actualArgs size (pushEnv envs none (decClock source))) with
    ⟨result, middle⟩
  rw [fix_clock_evaluate, actual] at safe
  rw [ret_call_cost wordOptimizerLocalPrice values names replacement l1 l2 destination arguments none
      source xs hg notBad actualArgs body size found badNames envs cut zero result middle actual,
    ret_call_cost wordOptimizerLocalPrice values names continuation l1 l2 destination arguments none
      source xs hg notBad actualArgs body size found badNames envs cut zero result middle actual]
  have nodeEq : wordOptimizerLocalPrice
      (.call (some (values, names, replacement, l1, l2)) destination arguments none) source =
      wordOptimizerLocalPrice
      (.call (some (values, names, continuation, l1, l2)) destination arguments none) source := by
    simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
  rw [nodeEq]
  apply Nat.add_le_add_left
  cases result with
  | none => simp [retCont]
  | some outcome =>
    cases outcome with
    | result location returned =>
      dsimp only [retCont]
      by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
      · simp only [invalid, if_true, Nat.le_refl]
      · simp only [invalid, if_false]
        rcases popped : popEnv middle with _ | post
        · simp only [popped, Nat.le_refl]
        · simp only [popped]
          by_cases domain : sptDomainEqUnion post.locals envs.1 envs.2
          · simp only [domain, if_true]
            apply next
            have selectedSafe := safe
            simp [invalid] at selectedSafe
            rw [popped] at selectedSafe
            simpa [domain] using selectedSafe
          · simp only [domain, if_false, Nat.le_refl]
    | _ => simp [retCont]

#print axioms optimizer_returning_none_continuation_cost_le

/-- The handler-bearing case uses the same actual callee state: pushEnv
stores handler labels but ignores handler code. Only the selected return or
exception continuation consumes its guarded recursive work bound. -/
theorem optimizer_returning_handler_continuation_cost_le {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (continuation replacement : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (destination : Option Nat) (arguments : List Nat)
    (register : Nat) (handler replacementHandler : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.call (some (values, names, continuation, l1, l2))
      destination arguments (some (register, handler, h1, h2))) source).1 ≠ some .error)
    (next : ∀ post : WordSemStateFiniteExact 64 C F,
      (evaluate continuation post).1 ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice replacement post ≤
        wordExecutionCost wordOptimizerLocalPrice continuation post)
    (handle : ∀ post : WordSemStateFiniteExact 64 C F,
      (evaluate handler post).1 ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice replacementHandler post ≤
        wordExecutionCost wordOptimizerLocalPrice handler post) :
    wordExecutionCost wordOptimizerLocalPrice
      (.call (some (values, names, replacement, l1, l2)) destination arguments
        (some (register, replacementHandler, h1, h2))) source ≤
    wordExecutionCost wordOptimizerLocalPrice
      (.call (some (values, names, continuation, l1, l2)) destination arguments
        (some (register, handler, h1, h2))) source := by
  rw [evaluate] at safe
  rcases hg : getVars arguments source with _ | xs
  · simp only [hg] at safe
    exact (safe rfl).elim
  simp only [hg] at safe
  by_cases bad : wordSemBadDestArgs destination arguments = true
  · simp only [bad, if_true] at safe
    exact (safe rfl).elim
  have notBad : wordSemBadDestArgs destination arguments = false := by simpa using bad
  simp only [bad, Bool.false_eq_true, if_false, wordSemAddRetLoc] at safe
  rcases found : wordSemFindCode destination (.loc l1 l2 :: xs) source.code source.stackSize with
    _ | ⟨actualArgs, body, size⟩
  · simp only [found] at safe
    exact (safe rfl).elim
  simp only [found] at safe
  by_cases badNames : sptDomainEmpty names.1 ∨ ¬ values.Nodup
  · simp only [badNames, if_true] at safe
    exact (safe rfl).elim
  simp only [badNames, if_false] at safe
  rcases cut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [cut] at safe
    exact (safe rfl).elim
  simp only [cut] at safe
  by_cases zero : source.clock = 0
  · rw [wordExecutionCost, wordExecutionCost]
    simp [hg, notBad, wordSemAddRetLoc, found, badNames, cut, zero,
      wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
  simp only [zero, dif_neg] at safe
  have envEq : pushEnv envs (some (register, replacementHandler, h1, h2)) (decClock source) =
      pushEnv envs (some (register, handler, h1, h2)) (decClock source) := rfl
  rcases actual : evaluate body (callEnv actualArgs size
      (pushEnv envs (some (register, handler, h1, h2)) (decClock source))) with ⟨result, middle⟩
  rw [fix_clock_evaluate, actual] at safe
  rw [ret_call_cost wordOptimizerLocalPrice values names replacement l1 l2 destination arguments
      (some (register, replacementHandler, h1, h2)) source xs hg notBad actualArgs body size found
      badNames envs cut zero result middle (by simpa only [envEq] using actual),
    ret_call_cost wordOptimizerLocalPrice values names continuation l1 l2 destination arguments
      (some (register, handler, h1, h2)) source xs hg notBad actualArgs body size found
      badNames envs cut zero result middle actual, envEq]
  have nodeEq : wordOptimizerLocalPrice
      (.call (some (values, names, replacement, l1, l2)) destination arguments
        (some (register, replacementHandler, h1, h2))) source =
      wordOptimizerLocalPrice
      (.call (some (values, names, continuation, l1, l2)) destination arguments
        (some (register, handler, h1, h2))) source := by
    simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
  rw [nodeEq]
  apply Nat.add_le_add_left
  cases result with
  | none => simp [retCont]
  | some outcome =>
    cases outcome with
    | result location returned =>
      dsimp only [retCont]
      by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
      · simp only [invalid, if_true, Nat.le_refl]
      · simp only [invalid, if_false]
        rcases popped : popEnv middle with _ | post
        · simp only [popped, Nat.le_refl]
        · simp only [popped]
          by_cases domain : sptDomainEqUnion post.locals envs.1 envs.2
          · simp only [domain, if_true]
            apply next
            have selectedSafe := safe
            simp [invalid] at selectedSafe
            rw [popped] at selectedSafe
            simpa [domain] using selectedSafe
          · simp only [domain, if_false, Nat.le_refl]
    | exception location value =>
      dsimp only [retCont]
      by_cases invalid : location ≠ .loc h1 h2
      · rw [if_pos invalid, if_pos invalid]
      · rw [if_neg invalid, if_neg invalid]
        by_cases domain : sptDomainEqUnion middle.locals envs.1 envs.2
        · simp only [domain, if_true]
          apply handle
          simpa [invalid, domain] using safe
        · simp only [domain, if_false, Nat.le_refl]
    | _ => simp [retCont]

#print axioms optimizer_returning_handler_continuation_cost_le
end InitECandidate.Runtime.FineCost
