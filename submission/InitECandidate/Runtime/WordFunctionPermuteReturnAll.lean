import InitECandidate.Runtime.WordFunctionPermuteExceptionCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 5000000

/-- Guarded callee/continuation induction; termination scopes require depth
as well as clock in the recursion measure. -/
def FunctionPermuteClockIH {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source : WordSemStateFiniteExact 64 C F) : Prop :=
  ∀ function p (state : WordSemStateFiniteExact 64 C F),
    Prod.Lex (· < ·) (· < ·) (state.termdep, state.clock) (source.termdep, source.clock) →
    FunctionPermuteCostGoal price function p state

theorem function_permute_cost_return {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (destination : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 C F) (ih : FunctionPermuteClockIH price source) :
    FunctionPermuteCostGoal price function (.call (some (values, names, continuation, l1, l2)) destination arguments handler) source := by
  intro finalPermutation safe
  have originalSafe := safe
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
  rcases found : wordSemFindCode destination (.loc l1 l2 :: xs) source.code source.stackSize with
    _ | ⟨actualArguments, body, size⟩
  · simp only [found] at safe
    exact (safe rfl).elim
  simp only [found] at safe
  by_cases invalidNames : sptDomainEmpty names.1 ∨ ¬ values.Nodup
  · simp only [invalidNames, if_true] at safe
    exact (safe rfl).elim
  simp only [invalidNames, if_false] at safe
  rcases cut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [cut] at safe
    exact (safe rfl).elim
  simp only [cut] at safe
  by_cases zero : source.clock = 0
  · obtain ⟨initialPermutation, run⟩ := permute_swap_lemma _ source finalPermutation originalSafe
    refine ⟨initialPermutation, run, ?_⟩
    conv_lhs => rw [wordFunctionExecutionCost]
    conv_rhs => rw [wordFunctionExecutionCost]
    simp only [getVars_withPermute, get]
    simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found, invalidNames, cut, zero, dite_true]
  simp only [zero, if_false] at safe
  let entry := WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))
  have smaller : Prod.Lex (· < ·) (· < ·)
      (entry.termdep, entry.clock) (source.termdep, source.clock) := by
    simp only [entry, WordSemStateFiniteExact.callEnv, pushEnv_clock, pushEnv_termdep, decClock]
    apply Prod.Lex.right
    omega
  have inner := ih ((wordCallLabel destination (.loc l1 l2 :: xs)).getD 0) body entry smaller
  rcases actual : evaluate body entry with ⟨result, post⟩
  have entryRun : evaluate body (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))) =
      (result, post) := actual
  rw [entryRun] at safe
  have postClock := evaluate_clock body entry result post actual
  have postSmaller : Prod.Lex (· < ·) (· < ·)
      (post.termdep, post.clock) (source.termdep, source.clock) := by
    simp only [entry, WordSemStateFiniteExact.callEnv, pushEnv_clock, pushEnv_termdep, decClock] at postClock
    rw [postClock.2]
    apply Prod.Lex.right
    omega
  cases result with
  | none => exact (safe rfl).elim
  | some outcome =>
    cases outcome with
    | result location returned =>
      apply function_permute_cost_normal_return price function values names continuation l1 l2 destination arguments handler
        source xs actualArguments body size get good found invalidNames envs cut zero location returned
        post entryRun inner ?_ finalPermutation originalSafe
      intro restored popped
      apply ih function continuation (setVars values returned restored)
      have dep := popEnv_termdep post restored popped
      have ck := popEnv_clock post restored popped
      simpa only [setVars, dep, ck] using postSmaller
    | exception location payload =>
      apply function_permute_cost_exception_return price function values names continuation l1 l2 destination arguments handler
        source xs actualArguments body size get good found invalidNames envs cut zero location payload
        post entryRun inner ?_ finalPermutation originalSafe
      intro reg handlerCode h1 h2 handlerEq
      apply ih function handlerCode (setVar reg payload post)
      simpa only [setVar] using postSmaller
    | «break» n => exact (safe rfl).elim
    | «continue» n => exact (safe rfl).elim
    | error => exact (safe rfl).elim
    | timeOut | notEnoughSpace | finalFfi event =>
      obtain ⟨bodyPermutation, bodyRun, bodyCost⟩ := inner finalPermutation (by rw [actual]; simp)
      rw [actual] at bodyRun
      let initialPermutation := permuteShift (source.permute 0) bodyPermutation
      let target := {source with permute := initialPermutation}
      have targetGet : getVars arguments target = some xs := by
        rw [show target = {source with permute := initialPermutation} from rfl, getVars_withPermute, get]
      have targetFound : wordSemFindCode destination (.loc l1 l2 :: xs) target.code target.stackSize =
          some (actualArguments, body, size) := found
      have targetCut : wordSemCutEnvs names target.locals = some envs := cut
      have targetNonzero : target.clock ≠ 0 := zero
      have targetEntry : WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock target)) =
          {entry with permute := bodyPermutation} := by
        exact congrArg (WordSemStateFiniteExact.callEnv actualArguments size)
          (pushEnv_permuteShift (decClock source) bodyPermutation envs handler)
      refine ⟨initialPermutation, ?_, ?_⟩
      · change evaluate _ target = _
        rw [WordToWord.evaluate_call_eq, WordToWord.evaluate_call_eq]
        simp only [targetGet, get, good, Bool.false_eq_true, if_false, wordSemAddRetLoc,
          targetFound, found, invalidNames, targetCut, cut, targetNonzero, zero]
        rw [targetEntry, bodyRun, entryRun]
      · change wordFunctionExecutionCost (fun fn p _ => price fn p) function _ target = _
        conv_lhs => rw [wordFunctionExecutionCost]
        conv_rhs => rw [wordFunctionExecutionCost]
        simp only [targetGet, get, good, Bool.false_eq_true, if_false, wordSemAddRetLoc,
          targetFound, found, invalidNames, targetCut, cut, targetNonzero, zero, dite_false]
        try rw [targetEntry]
        try simp only [fix_clock_evaluate]
        rw [bodyRun, entryRun, bodyCost]
        rfl

#print axioms function_permute_cost_return
end InitECandidate.Runtime.FineCost
