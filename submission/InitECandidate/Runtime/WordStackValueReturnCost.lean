import InitECandidate.Runtime.WordStackValueCallFrames

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
open Flapjack.WordSemStackEq
set_option maxHeartbeats 6000000

/-- Normal-return constructor for value-equal saved-stack cost transport.
The actual callee run and stack-swap semantics derive the restored target
caller; no independent target result or popped-frame premise is supplied. -/
theorem stack_value_cost_normal_return {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
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
    (actual : evaluate body (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))) =
      (some (.result location returned), post))
    (inner : StackValueCostGoal price body (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))))
    (next : ∀ restored, popEnv post = some restored →
      StackValueCostGoal price continuation (setVars values returned restored)) :
    StackValueCostGoal price (.call (some (values, names, continuation, l1, l2)) destination arguments handler) source := by
  intro safe stack related
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
    let entry := WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))
    let target := {source with stack := stack}
    obtain ⟨frame, shape, entrySwap, extended⟩ := pushed_callee_stack_value (decClock source) stack
      envs handler actualArguments size related
    have targetEntry : WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock target)) =
        {entry with stack := frame :: stack} := by
      have decrement : decClock target = {(decClock source) with stack := stack} := rfl
      rw [decrement]
      exact entrySwap
    have transport := evaluateStackSwap body entry
    unfold stackSwapPost at transport
    rw [show evaluate body entry = (some (.result location returned), post) from actual] at transport
    obtain ⟨targetStack, swapped, stackValues, targetKeys⟩ := transport.2.2 (frame :: stack) extended
    have sourceKeys : sKeyEq (frame :: source.stack) post.stack := by
      have entryShape : entry.stack = frame :: source.stack := shape
      rw [← entryShape]
      exact transport.1
    obtain ⟨common, sourceTail, targetTail, sourceShape, targetShape, tailValues⟩ :=
      same_pushed_frame_head frame source.stack stack post.stack targetStack sourceKeys targetKeys stackValues
    have mappedPop := (pop_same_frame_stack_value post restored common sourceTail targetTail sourceShape tailValues popped).1
    have restoredValues := (pop_same_frame_stack_value post restored common sourceTail targetTail sourceShape tailValues popped).2
    have targetBodyRun : evaluate body (WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock target))) =
        (some (.result location returned), {post with stack := targetStack}) := by
      rw [targetEntry]
      exact swapped
    have bodySafe : (evaluate body entry).1 ≠ some .error := by
      rw [show evaluate body entry = (some (.result location returned), post) from actual]
      simp
    have bodyCost := inner bodySafe (frame :: stack) extended
    have nextCost := next restored popped safe targetTail restoredValues
    have targetGet : getVars arguments target = some xs := by
      rw [show target = {source with stack := stack} from rfl, getVars_withStack, get]
    have targetFound : wordSemFindCode destination (.loc l1 l2 :: xs) target.code target.stackSize =
        some (actualArguments, body, size) := found
    have targetCut : wordSemCutEnvs names target.locals = some envs := cut
    have targetNonzero : target.clock ≠ 0 := nonzero
    change wordExecutionCost (fun p _ => price p) _ target = _
    rw [ret_call_cost (fun p _ => price p) values names continuation l1 l2 destination arguments handler
      target xs targetGet good actualArguments body size targetFound validNames envs targetCut targetNonzero
      (some (.result location returned)) _ targetBodyRun]
    rw [ret_call_cost (fun p _ => price p) values names continuation l1 l2 destination arguments handler
      source xs get good actualArguments body size found validNames envs cut nonzero
      (some (.result location returned)) post actual]
    simp only [retCont, invalid, if_false, targetShape, mappedPop, popped, domain, if_true]
    rw [targetEntry, bodyCost]
    exact congrArg (fun n => price (.call (some (values, names, continuation, l1, l2)) destination arguments handler) +
      wordExecutionCost (fun p _ => price p) body entry + n) nextCost
  · simp only [domain, if_false] at safe
    exact (safe rfl).elim

#print axioms stack_value_cost_normal_return
end InitECandidate.Runtime.FineCost
