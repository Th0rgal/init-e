import InitECandidate.Runtime.WordStackValueExceptionCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
open Flapjack.WordSemStackEq
set_option maxHeartbeats 5000000

/-- Guarded callee/continuation induction; termination scopes require depth
as well as clock in the recursion measure. -/
def StackValueClockIH {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (source : WordSemStateFiniteExact 64 C F) : Prop :=
  ∀ p (state : WordSemStateFiniteExact 64 C F),
    Prod.Lex (· < ·) (· < ·) (state.termdep, state.clock) (source.termdep, source.clock) →
    StackValueCostGoal price p state

theorem stack_value_cost_return {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (destination : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 C F) (ih : StackValueClockIH price source) :
    StackValueCostGoal price (.call (some (values, names, continuation, l1, l2)) destination arguments handler) source := by
  intro safe stack related
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
  · conv_lhs => rw [wordExecutionCost]
    conv_rhs => rw [wordExecutionCost]
    simp only [getVars_withStack, get]
    simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found, invalidNames, cut, zero, dite_true]
  simp only [zero, if_false] at safe
  let entry := WordSemStateFiniteExact.callEnv actualArguments size (pushEnv envs handler (decClock source))
  have smaller : Prod.Lex (· < ·) (· < ·)
      (entry.termdep, entry.clock) (source.termdep, source.clock) := by
    simp only [entry, WordSemStateFiniteExact.callEnv, pushEnv_clock, pushEnv_termdep, decClock]
    apply Prod.Lex.right
    omega
  have inner := ih body entry smaller
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
      apply stack_value_cost_normal_return price values names continuation l1 l2 destination arguments handler
        source xs actualArguments body size get good found invalidNames envs cut zero location returned
        post entryRun inner ?_ originalSafe stack related
      intro restored popped
      apply ih continuation (setVars values returned restored)
      have dep := popEnv_termdep post restored popped
      have ck := popEnv_clock post restored popped
      simpa only [setVars, dep, ck] using postSmaller
    | exception location payload =>
      apply stack_value_cost_exception_return price values names continuation l1 l2 destination arguments handler
        source xs actualArguments body size get good found invalidNames envs cut zero location payload
        post entryRun inner ?_ originalSafe stack related
      intro reg handlerCode h1 h2 handlerEq
      apply ih handlerCode (setVar reg payload post)
      simpa only [setVar] using postSmaller
    | «break» n => exact (safe rfl).elim
    | «continue» n => exact (safe rfl).elim
    | error => exact (safe rfl).elim
    | timeOut | notEnoughSpace | finalFfi event =>
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
      rw [actual] at transport
      have targetBodyRun := transport.2.2 (frame :: stack) extended
      rw [← targetEntry] at targetBodyRun
      have bodySafe : (evaluate body entry).1 ≠ some .error := by rw [actual]; simp
      have bodyCost := inner bodySafe (frame :: stack) extended
      have targetGet : getVars arguments target = some xs := by
        rw [show target = {source with stack := stack} from rfl, getVars_withStack, get]
      have targetFound : wordSemFindCode destination (.loc l1 l2 :: xs) target.code target.stackSize =
          some (actualArguments, body, size) := found
      have targetCut : wordSemCutEnvs names target.locals = some envs := cut
      have targetNonzero : target.clock ≠ 0 := zero
      change wordExecutionCost (fun p _ => price p) _ target = _
      rw [ret_call_cost (fun p _ => price p) values names continuation l1 l2 destination arguments handler
        target xs targetGet good actualArguments body size targetFound invalidNames envs targetCut targetNonzero
        _ _ targetBodyRun]
      rw [ret_call_cost (fun p _ => price p) values names continuation l1 l2 destination arguments handler
        source xs get good actualArguments body size found invalidNames envs cut zero _ post entryRun]
      simp only [retCont, Nat.add_zero]
      rw [targetEntry, bodyCost]

#print axioms stack_value_cost_return
end InitECandidate.Runtime.FineCost
