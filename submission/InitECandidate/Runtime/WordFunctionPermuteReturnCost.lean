import InitECandidate.Runtime.WordFunctionPermuteTailCost
import InitECandidate.Runtime.WordFunctionCallCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 5000000

/-- Stitch a successful normal return backwards through the restored caller
and the callee. The saved-frame permutation head is retained exactly. -/
theorem function_permute_cost_normal_return {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
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
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (post : WordSemStateFiniteExact 64 C F)
    (actual : evaluate body (callEnv actualArguments size (pushEnv envs handler (decClock source))) =
      (some (.result location returned), post))
    (inner : FunctionPermuteCostGoal price ((wordCallLabel destination (.loc l1 l2 :: xs)).getD 0) body (callEnv actualArguments size (pushEnv envs handler (decClock source))))
    (next : ∀ restored, popEnv post = some restored →
      FunctionPermuteCostGoal price function continuation (setVars values returned restored)) :
    FunctionPermuteCostGoal price function (.call (some (values, names, continuation, l1, l2)) destination arguments handler) source := by
  intro finalPermutation safe
  have sourceEq := WordToWord.evaluate_call_eq source
    (some (values, names, continuation, l1, l2)) handler destination arguments
  simp only [get, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found,
    validNames, cut, nonzero, actual] at sourceEq
  rw [sourceEq] at safe
  by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
  · simp only [invalid, if_true] at safe
    exact (safe rfl).elim
  simp only [invalid, if_false] at safe
  rcases popped : popEnv post with _ | restored
  · simp only [popped] at safe
    exact (safe rfl).elim
  simp only [popped] at safe
  by_cases domain : sptDomainEqUnion restored.locals envs.1 envs.2
  · simp only [domain, if_true] at safe
    obtain ⟨middlePermutation, nextRun, nextCost⟩ := next restored popped finalPermutation safe
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
        (some (.result location returned), {post with permute := middlePermutation}) := by
      rw [targetEntry]
      exact bodyRun
    have mappedPop : popEnv {post with permute := middlePermutation} =
        some {restored with permute := middlePermutation} := by
      rw [popEnv_withPermute, popped]
      rfl
    have targetEq := WordToWord.evaluate_call_eq target
      (some (values, names, continuation, l1, l2)) handler destination arguments
    simp only [targetGet, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, targetFound,
      validNames, targetCut, targetNonzero, targetRun] at targetEq
    refine ⟨initialPermutation, ?_, ?_⟩
    · change evaluate _ target = _
      rw [targetEq, sourceEq]
      simp only [invalid, if_false, mappedPop, popped, domain, if_true]
      exact nextRun
    · change wordFunctionExecutionCost (fun fn p _ => price fn p) function _ target = _
      rw [function_ret_call_cost (fun fn p _ => price fn p) function values names continuation l1 l2 destination arguments handler
        target xs targetGet good actualArguments body size targetFound validNames envs targetCut targetNonzero
        (some (.result location returned)) _ targetRun]
      rw [function_ret_call_cost (fun fn p _ => price fn p) function values names continuation l1 l2 destination arguments handler
        source xs get good actualArguments body size found validNames envs cut nonzero
        (some (.result location returned)) post actual]
      simp only [wordFunctionRetCont, invalid, if_false, mappedPop, popped, domain, if_true]
      rw [targetEntry, bodyCost]
      exact congrArg (fun n => price function (.call (some (values, names, continuation, l1, l2)) destination arguments handler) +
        wordFunctionExecutionCost (fun fn p _ => price fn p) ((wordCallLabel destination (.loc l1 l2 :: xs)).getD 0) body
          (callEnv actualArguments size (pushEnv envs handler (decClock source))) + n) nextCost
  · simp only [domain, if_false] at safe
    exact (safe rfl).elim

#print axioms function_permute_cost_normal_return
end InitECandidate.Runtime.FineCost
