import InitECandidate.Runtime.WordFunctionPermuteReturnCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 5000000

/-- Exception dispatch stitches the actual selected handler, or preserves
an escaping exception without charging an unexecuted continuation. -/
theorem function_permute_cost_exception_return {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (destination : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 C F) (xs actualArguments : List (WordLocW 64))
    (body : WordLangProgHOL (BitVec 64)) (size : Option Nat)
    (get : getVars arguments source = some xs)
    (good : wordSemBadDestArgs destination arguments = false)
    (found : wordSemFindCode destination (.loc l1 l2 :: xs) source.code source.stackSize =
      some (actualArguments, body, size))
    (validNames : ¬ (sptDomainEmpty names.1 ∨ ¬ values.Nodup))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (cut : wordSemCutEnvs names source.locals = some envs) (nonzero : source.clock ≠ 0)
    (location : WordLocW 64) (payload : WordLocW 64)
    (post : WordSemStateFiniteExact 64 C F)
    (actual : evaluate body (callEnv actualArguments size (pushEnv envs handler (decClock source))) =
      (some (.exception location payload), post))
    (inner : FunctionPermuteCostGoal price ((wordCallLabel destination (.loc l1 l2 :: xs)).getD 0) body (callEnv actualArguments size (pushEnv envs handler (decClock source))))
    (next : ∀ reg handlerCode h1 h2, handler = some (reg, handlerCode, h1, h2) →
      FunctionPermuteCostGoal price function handlerCode (setVar reg payload post)) :
    FunctionPermuteCostGoal price function (.call (some (values, names, continuation, l1, l2)) destination arguments handler) source := by
  intro finalPermutation safe
  have sourceEq := WordToWord.evaluate_call_eq source
    (some (values, names, continuation, l1, l2)) handler destination arguments
  simp only [get, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found,
    validNames, cut, nonzero, actual] at sourceEq
  rw [sourceEq] at safe
  suffices chosen : ∃ middlePermutation,
      (match (generalizing := false) handler with
       | none => True
       | some (reg, handlerCode, h1, h2) =>
         evaluate handlerCode {(setVar reg payload post) with permute := middlePermutation} =
           ((evaluate handlerCode (setVar reg payload post)).1,
             {(evaluate handlerCode (setVar reg payload post)).2 with permute := finalPermutation}) ∧
         wordFunctionExecutionCost (fun fn p _ => price fn p) function handlerCode
             {(setVar reg payload post) with permute := middlePermutation} =
           wordFunctionExecutionCost (fun fn p _ => price fn p) function handlerCode (setVar reg payload post)) ∧
      (handler = none → middlePermutation = finalPermutation) by
    obtain ⟨middlePermutation, selected, escape⟩ := chosen
    obtain ⟨bodyPermutation, bodyRun, bodyCost⟩ := inner middlePermutation (by rw [actual]; simp)
    rw [actual] at bodyRun
    let initialPermutation := permuteShift (source.permute 0) bodyPermutation
    let target := {source with permute := initialPermutation}
    have targetGet : getVars arguments target = some xs := by
      rw [show target = {source with permute := initialPermutation} from rfl, getVars_withPermute, get]
    have targetFound : wordSemFindCode destination (.loc l1 l2 :: xs) target.code target.stackSize =
        some (actualArguments, body, size) := found
    have targetCut : wordSemCutEnvs names target.locals = some envs := cut
    have targetNonzero : target.clock ≠ 0 := nonzero
    have targetEntry : callEnv actualArguments size (pushEnv envs handler (decClock target)) =
        {callEnv actualArguments size (pushEnv envs handler (decClock source)) with permute := bodyPermutation} := by
      exact congrArg (callEnv actualArguments size)
        (pushEnv_permuteShift (decClock source) bodyPermutation envs handler)
    have targetRun : evaluate body (callEnv actualArguments size (pushEnv envs handler (decClock target))) =
        (some (.exception location payload), {post with permute := middlePermutation}) := by
      rw [targetEntry]
      exact bodyRun
    have targetEq := WordToWord.evaluate_call_eq target
      (some (values, names, continuation, l1, l2)) handler destination arguments
    simp only [targetGet, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, targetFound,
      validNames, targetCut, targetNonzero, targetRun] at targetEq
    have costSource := function_ret_call_cost (fun fn p _ => price fn p) function values names continuation l1 l2 destination arguments handler
      source xs get good actualArguments body size found validNames envs cut nonzero
      (some (.exception location payload)) post actual
    have costTarget := function_ret_call_cost (fun fn p _ => price fn p) function values names continuation l1 l2 destination arguments handler
      target xs targetGet good actualArguments body size targetFound validNames envs targetCut targetNonzero
      (some (.exception location payload)) _ targetRun
    refine ⟨initialPermutation, ?_, ?_⟩
    · change evaluate _ target = _
      rw [targetEq, sourceEq]
      rcases handlerEq : handler with _ | ⟨reg, handlerCode, h1, h2⟩
      · have same := escape handlerEq
        simp only [handlerEq, same]
      · simp only [handlerEq] at selected safe ⊢
        by_cases invalid : location ≠ .loc h1 h2
        · rw [if_pos invalid] at safe
          exact (safe rfl).elim
        simp only [invalid, if_false] at safe ⊢
        by_cases domain : sptDomainEqUnion post.locals envs.1 envs.2
        · simp only [domain, if_true]
          exact selected.1
        · simp only [domain, if_false] at safe
          exact (safe rfl).elim
    · change wordFunctionExecutionCost (fun fn p _ => price fn p) function _ target = _
      rw [costTarget, costSource, targetEntry, bodyCost]
      apply congrArg (fun n => price function (.call (some (values, names, continuation, l1, l2)) destination arguments handler) +
        wordFunctionExecutionCost (fun fn p _ => price fn p) ((wordCallLabel destination (.loc l1 l2 :: xs)).getD 0) body
          (callEnv actualArguments size (pushEnv envs handler (decClock source))) + n)
      rcases handlerEq : handler with _ | ⟨reg, handlerCode, h1, h2⟩
      · simp only [wordFunctionRetCont, handlerEq]
      · simp only [handlerEq] at selected safe
        by_cases invalid : location ≠ .loc h1 h2
        · rw [if_pos invalid] at safe
          exact (safe rfl).elim
        by_cases domain : sptDomainEqUnion post.locals envs.1 envs.2
        · simp only [wordFunctionRetCont, handlerEq, invalid, if_false, domain, if_true]
          exact selected.2
        · simp only [invalid, if_false, domain] at safe
          exact (safe rfl).elim
  rcases handlerEq : handler with _ | ⟨reg, handlerCode, h1, h2⟩
  · exact ⟨finalPermutation, True.intro, fun _ => rfl⟩
  · simp only [handlerEq] at safe
    by_cases invalid : location ≠ .loc h1 h2
    · rw [if_pos invalid] at safe
      exact (safe rfl).elim
    simp only [invalid, if_false] at safe
    by_cases domain : sptDomainEqUnion post.locals envs.1 envs.2
    · simp only [domain, if_true] at safe
      obtain ⟨middlePermutation, run, cost⟩ := next reg handlerCode h1 h2 handlerEq finalPermutation safe
      refine ⟨middlePermutation, ?_, ?_⟩
      · simpa only [handlerEq] using And.intro run cost
      · simp only [handlerEq, reduceCtorEq, false_implies]
    · simp only [domain, if_false] at safe
      exact (safe rfl).elim

#print axioms function_permute_cost_exception_return
end InitECandidate.Runtime.FineCost
