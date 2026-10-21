import InitECandidate.Runtime.WordStackValueLoopCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
open Flapjack.WordSemStackEq
set_option maxHeartbeats 4000000

/-- A tail call executes the same selected callee over the substituted saved
stack. `callEnv_withStack` discharges the actual stack-size/max alignment. -/
theorem stack_value_cost_tail {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (destination : Option Nat) (arguments : List Nat) (source : WordSemStateFiniteExact 64 C F)
    (inner : ∀ xs actualArguments body size,
      getVars arguments source = some xs →
      wordSemFindCode destination xs source.code source.stackSize = some (actualArguments, body, size) →
      source.clock ≠ 0 → StackValueCostGoal price body (WordSemStateFiniteExact.callEnv actualArguments size (decClock source))) :
    StackValueCostGoal price (.call none destination arguments none) source := by
  intro safe stack related
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
  let target := {source with stack := stack}
  have targetGet : getVars arguments target = some xs := by
    rw [show target = {source with stack := stack} from rfl, getVars_withStack, get]
  have targetFound : wordSemFindCode destination xs target.code target.stackSize =
      some (actualArguments, body, size) := found
  by_cases zero : source.clock = 0
  · conv_lhs => rw [wordExecutionCost]
    conv_rhs => rw [wordExecutionCost]
    simp only [getVars_withStack, get]
    simp only [good, Bool.false_eq_true, if_false, wordSemAddRetLoc, found, zero, dite_true]
  simp only [zero, if_false] at safe
  let entry := WordSemStateFiniteExact.callEnv actualArguments size (decClock source)
  rcases actual : evaluate body entry with ⟨result, post⟩
  have entryRun : evaluate body (WordSemStateFiniteExact.callEnv actualArguments size (decClock source)) = (result, post) := actual
  rw [entryRun] at safe
  have bodySafe : (evaluate body entry).1 ≠ some .error := by
    rw [actual]
    change result ≠ some .error
    intro error
    subst result
    simp [wordSemBadFunReturn] at safe
  have entryStack : entry.stack = source.stack := rfl
  have entryRelated : sValEq entry.stack stack := entryStack.symm ▸ related
  have bodyCost := inner xs actualArguments body size get found zero bodySafe stack entryRelated
  have targetEntry : WordSemStateFiniteExact.callEnv actualArguments size (decClock target) =
      {entry with stack := stack} := by
    have decrement : decClock target = {(decClock source) with stack := stack} := rfl
    rw [decrement]
    exact callEnv_withStack actualArguments size (decClock source) stack related
  change wordExecutionCost (fun p _ => price p) _ target = _
  have targetNonzero : target.clock ≠ 0 := zero
  rw [tail_call_cost (fun p _ => price p) destination arguments target xs targetGet good
      actualArguments body size targetFound targetNonzero]
  rw [tail_call_cost (fun p _ => price p) destination arguments source xs get good
      actualArguments body size found zero]
  rw [targetEntry, bodyCost]

#print axioms stack_value_cost_tail
end InitECandidate.Runtime.FineCost
