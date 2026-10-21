import InitECandidate.Runtime.WordStackValueReturnCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
open Flapjack.WordSemStackEq
set_option maxHeartbeats 6000000

/-- Exception constructor of the quantitative stack-swap proof. A caught
exception restores the identical top frame; an escaping exception executes
no continuation. Both cases derive the actual target body run. -/
theorem stack_value_cost_exception_return {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
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
    (actual : evaluate body (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))) =
      (some (.exception location payload), post))
    (inner : StackValueCostGoal price body (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))))
    (next : ∀ reg handlerCode h1 h2, handler = some (reg, handlerCode, h1, h2) →
      StackValueCostGoal price handlerCode (setVar reg payload post)) :
    StackValueCostGoal price (.call (some (values, names, continuation, l1, l2)) destination arguments handler) source := by
  intro safe stack related
  have sourceEq := WordToWord.evaluate_call_eq source
    (some (values, names, continuation, l1, l2)) handler destination arguments
  simp only [get, good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found,
    validNames, cut, nonzero, actual] at sourceEq
  rw [sourceEq] at safe
  let entry := WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))
  let target := {source with stack := stack}
  obtain ⟨frame, shape, entrySwap, extended⟩ := pushed_callee_stack_value (decClock source) stack
    envs handler actualArguments size related
  have targetEntry : WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock target)) =
      {entry with stack := frame :: stack} := by
    have decrement : decClock target = {(decClock source) with stack := stack} := rfl
    rw [decrement]
    exact entrySwap
  have bodySafe : (evaluate body entry).1 ≠ some .error := by
    rw [show evaluate body entry = (some (.exception location payload), post) from actual]
    simp
  have bodyCost := inner bodySafe (frame :: stack) extended
  have targetGet : getVars arguments target = some xs := by
    rw [show target = {source with stack := stack} from rfl, getVars_withStack, get]
  have targetFound : wordSemFindCode destination (.loc l1 l2 :: xs) target.code target.stackSize =
      some (actualArguments, body, size) := found
  have targetCut : wordSemCutEnvs names target.locals = some envs := cut
  have targetNonzero : target.clock ≠ 0 := nonzero
  change wordExecutionCost (fun p _ => price p) _ target = _
  cases handler with
  | none =>
    have same := stack_value_result body entry (frame :: stack) extended bodySafe
    rw [show evaluate body entry = (some (.exception location payload), post) from actual] at same
    rcases targetRun : evaluate body (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs none (decClock target))) with
      ⟨targetResult, targetPost⟩
    have resultEq : targetResult = some (.exception location payload) := by
      rw [← targetEntry, targetRun] at same
      exact same
    subst targetResult
    rw [ret_call_cost (fun p _ => price p) values names continuation l1 l2 destination arguments none
      target xs targetGet good actualArguments body size targetFound validNames envs targetCut targetNonzero
      (some (.exception location payload)) _ targetRun]
    rw [ret_call_cost (fun p _ => price p) values names continuation l1 l2 destination arguments none
      source xs get good actualArguments body size found validNames envs cut nonzero
      (some (.exception location payload)) post actual]
    simp only [retCont]
    rw [targetEntry, bodyCost]
  | some bundle =>
    rcases bundle with ⟨reg, handlerCode, h1, h2⟩
    dsimp only at safe
    by_cases invalid : location ≠ .loc h1 h2
    · rw [if_pos invalid] at safe
      exact (safe rfl).elim
    simp only [invalid, if_false] at safe
    by_cases domain : sptDomainEqUnion post.locals envs.1 envs.2
    · simp only [domain, if_true] at safe
      have top : entry.handler + 1 = entry.stack.length := by
        simp only [entry, WordSemStateFiniteExact.callEnv, pushEnv, List.length_cons]
      have entryShape : entry.stack = frame :: source.stack := shape
      obtain ⟨afterStack, swapped, afterValues⟩ := stack_value_top_exception body entry post location payload
        frame source.stack stack entryShape top extended actual
      have targetBodyRun : evaluate body (WordSemStateFiniteExact.callEnv actualArguments size
          (pushEnv envs (some (reg, handlerCode, h1, h2)) (decClock target))) =
          (some (.exception location payload), {post with stack := afterStack}) := by
        rw [targetEntry]
        exact swapped
      have nextCost := next reg handlerCode h1 h2 rfl safe afterStack afterValues
      rw [ret_call_cost (fun p _ => price p) values names continuation l1 l2 destination arguments
        (some (reg, handlerCode, h1, h2)) target xs targetGet good actualArguments body size targetFound validNames
        envs targetCut targetNonzero (some (.exception location payload)) _ targetBodyRun]
      rw [ret_call_cost (fun p _ => price p) values names continuation l1 l2 destination arguments
        (some (reg, handlerCode, h1, h2)) source xs get good actualArguments body size found validNames envs cut
        nonzero (some (.exception location payload)) post actual]
      simp only [retCont, invalid, if_false, domain, if_true]
      rw [targetEntry, bodyCost]
      exact congrArg (fun n => price (.call (some (values, names, continuation, l1, l2)) destination arguments
          (some (reg, handlerCode, h1, h2))) + wordExecutionCost (fun p _ => price p) body entry + n) nextCost
    · simp only [domain, if_false] at safe
      exact (safe rfl).elim

#print axioms stack_value_cost_exception_return
end InitECandidate.Runtime.FineCost
