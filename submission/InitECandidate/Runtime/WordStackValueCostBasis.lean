import InitECandidate.Runtime.WordPermuteGlobalCost
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
open Flapjack.WordSemStackEq
set_option maxHeartbeats 4000000

/-- Saved frame keys may be renamed by SSA; their values are preserved. The
counter follows the same non-error run with that value-equal stack. -/
def StackValueCostGoal {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) : Prop :=
  (evaluate program source).1 ≠ some .error →
    ∀ stack, sValEq source.stack stack →
      wordExecutionCost (fun p _ => price p) program {source with stack := stack} =
        wordExecutionCost (fun p _ => price p) program source

theorem stack_values_iff_forall2 (left right : List (WordSemStackFrame 64)) :
    sValEq left right ↔ List.Forall₂ sFrameValEq left right := by
  induction left generalizing right with
  | nil => cases right <;> simp [sValEq]
  | cons head rest ih =>
    cases right with
    | nil => simp [sValEq]
    | cons head' rest' => simp [sValEq, ih, and_comm]

theorem stack_values_append (left right a b : List (WordSemStackFrame 64))
    (one : sValEq left right) (two : sValEq a b) : sValEq (left ++ a) (right ++ b) := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [sValEq]
  | cons head rest ih =>
    cases right with
    | nil => simp [sValEq] at one
    | cons head' rest' => exact ⟨ih rest' one.1, one.2⟩

theorem stack_values_reverse (left right : List (WordSemStackFrame 64))
    (related : sValEq left right) : sValEq left.reverse right.reverse := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [sValEq]
  | cons head rest ih =>
    cases right with
    | nil => simp [sValEq] at related
    | cons head' rest' =>
      rw [List.reverse_cons, List.reverse_cons]
      exact stack_values_append _ _ _ _ (ih rest' related.1) ⟨True.intro, related.2⟩

theorem stack_values_take (left right : List (WordSemStackFrame 64)) (n : Nat)
    (related : sValEq left right) : sValEq (left.take n) (right.take n) := by
  induction n generalizing left right with
  | zero => trivial
  | succ n ih =>
    cases left <;> cases right
    all_goals first
      | trivial
      | exact related.elim
      | exact ⟨ih _ _ related.1, related.2⟩

theorem stack_values_lastN (left right : List (WordSemStackFrame 64)) (n : Nat)
    (related : sValEq left right) : sValEq (wordSemLastN n left) (wordSemLastN n right) := by
  unfold wordSemLastN
  exact stack_values_reverse _ _ (stack_values_take _ _ n (stack_values_reverse _ _ related))

/-- The total stack-swap semantics exposes the same result for every
value-equal stack, including an escaping exception's actual handler frame. -/
theorem stack_value_result {C F : Type} (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F) (stack : List (WordSemStackFrame 64))
    (related : sValEq source.stack stack) (safe : (evaluate program source).1 ≠ some .error) :
    (evaluate program {source with stack := stack}).1 = (evaluate program source).1 := by
  have transport := evaluateStackSwap program source
  unfold stackSwapPost at transport
  rcases actual : evaluate program source with ⟨result, post⟩
  rw [actual] at transport safe
  cases result with
  | none =>
    obtain ⟨_, _, swapped⟩ := transport
    obtain ⟨afterStack, run, _⟩ := swapped stack related
    have resultEq := congrArg Prod.fst run
    exact resultEq
  | some outcome =>
    cases outcome with
    | error => exact (safe rfl).elim
    | timeOut | notEnoughSpace | finalFfi event =>
      have resultEq := congrArg Prod.fst (transport.2.2 stack related)
      exact resultEq
    | result _ _ | «break» _ | «continue» _ =>
      obtain ⟨afterStack, run, _⟩ := transport.2.2 stack related
      have resultEq := congrArg Prod.fst run
      exact resultEq
    | exception location payload =>
      obtain ⟨bounded, first, roots, handler, tail, size, returned, frame, sameSize, locals, keys, handlerEq, swapped⟩ := transport
      have tailRelated := stack_values_lastN source.stack stack (source.handler + 1) related
      rw [frame] at tailRelated
      rcases targetFrame : wordSemLastN (source.handler + 1) stack with _ | ⟨head, rest⟩
      · simp only [targetFrame, sValEq] at tailRelated
      · rcases head with ⟨newSize, newFirst, newRoots, newHandler⟩
        simp only [targetFrame, sValEq, sFrameValEqDef2] at tailRelated
        have handlerSame := tailRelated.2.2.1
        have sizeSame := tailRelated.2.2.2
        subst newHandler
        subst newSize
        obtain ⟨afterStack, afterLocals, run, _⟩ := swapped stack newFirst newRoots rest ⟨targetFrame, related⟩
        have resultEq := congrArg Prod.fst run
        exact resultEq

/-- A fall-through prefix preserves every field except its renamed stack.
This gives the actual related suffix entry needed by quantitative recursion. -/
theorem stack_value_none {C F : Type} (program : WordLangProgHOL (BitVec 64))
    (source post : WordSemStateFiniteExact 64 C F) (stack : List (WordSemStackFrame 64))
    (actual : evaluate program source = (none, post)) (related : sValEq source.stack stack) :
    ∃ afterStack, evaluate program {source with stack := stack} = (none, {post with stack := afterStack}) ∧
      sValEq post.stack afterStack := by
  have transport := evaluateStackSwap program source
  unfold stackSwapPost at transport
  rw [actual] at transport
  obtain ⟨afterStack, run, values, _⟩ := transport.2.2 stack related
  exact ⟨afterStack, run, values⟩

theorem stack_value_cost_atomic {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (atomic : wordCostAtomic program = true) : StackValueCostGoal price program source := by
  intro safe stack related
  rw [wordExecutionCost_atomic _ _ _ atomic, wordExecutionCost_atomic _ _ _ atomic]

theorem stack_value_cost_seq {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (first second : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (one : StackValueCostGoal price first source)
    (two : ∀ middle, evaluate first source = (none, middle) → StackValueCostGoal price second middle) :
    StackValueCostGoal price (.seq first second) source := by
  intro safe stack related
  rcases actual : evaluate first source with ⟨result, middle⟩
  have firstSafe : (evaluate first source).1 ≠ some .error := by
    intro bad
    have error : result = some .error := by simpa only [actual] using bad
    rw [evaluate, fix_clock_evaluate, actual, error] at safe
    exact (safe rfl).elim
  have firstCost := one firstSafe stack related
  have sameResult := stack_value_result first source stack related firstSafe
  rw [actual] at sameResult
  rw [wordExecutionCost_seq, wordExecutionCost_seq, actual, firstCost]
  cases result with
  | none =>
    have secondSafe : (evaluate second middle).1 ≠ some .error := by
      rw [evaluate, fix_clock_evaluate, actual] at safe
      exact safe
    obtain ⟨afterStack, swapped, values⟩ := stack_value_none first source middle stack actual related
    rw [swapped]
    exact congrArg (fun n => price (.seq first second) + wordExecutionCost (fun p _ => price p) first source + n)
      (two middle actual secondSafe afterStack values)
  | some outcome =>
    rcases targetRun : evaluate first {source with stack := stack} with ⟨targetResult, targetPost⟩
    have equal : targetResult = some outcome := by simpa only [targetRun] using sameResult
    rw [equal]

#print axioms stack_values_iff_forall2
#print axioms stack_values_lastN
#print axioms stack_value_result
#print axioms stack_value_none
#print axioms stack_value_cost_atomic
#print axioms stack_value_cost_seq
end InitECandidate.Runtime.FineCost
