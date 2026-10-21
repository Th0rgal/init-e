import InitECandidate.Runtime.WordFunctionCostProps
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwap
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Control

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Cost-aware permutation stitching. This chooses a new input permutation
for a requested final permutation, preserving the actual result, every other
post-state field and executed cost. It does not assert equality for arbitrary
independently chosen input permutations. -/
def FunctionPermuteCostGoal {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F) : Prop :=
  ∀ finalPermutation : Nat → Nat → Nat,
    (evaluate program source).1 ≠ some .error →
    ∃ initialPermutation,
      evaluate program {source with permute := initialPermutation} =
        ((evaluate program source).1, {(evaluate program source).2 with permute := finalPermutation}) ∧
      wordFunctionExecutionCost (fun fn p _ => price fn p) function program {source with permute := initialPermutation} =
        wordFunctionExecutionCost (fun fn p _ => price fn p) function program source

theorem function_permute_cost_atomic {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (atomic : wordCostAtomic program = true) : FunctionPermuteCostGoal price function program source := by
  intro finalPermutation safe
  obtain ⟨initialPermutation, run⟩ := permute_swap_lemma program source finalPermutation safe
  refine ⟨initialPermutation, run, ?_⟩
  rw [wordFunctionExecutionCost_atomic _ _ _ _ atomic, wordFunctionExecutionCost_atomic _ _ _ _ atomic]

/-- Sequence stitching works backwards: choose the suffix's input
permutation, then make the actual prefix end with that permutation. -/
theorem function_permute_cost_seq {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (first second : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (one : FunctionPermuteCostGoal price function first source)
    (two : ∀ middle, evaluate first source = (none, middle) → FunctionPermuteCostGoal price function second middle) :
    FunctionPermuteCostGoal price function (.seq first second) source := by
  intro finalPermutation safe
  rcases actual : evaluate first source with ⟨result, middle⟩
  have firstSafe : (evaluate first source).1 ≠ some .error := by
    intro bad
    have error : result = some .error := by simpa only [actual] using bad
    rw [evaluate, fix_clock_evaluate, actual, error] at safe
    exact safe rfl
  cases result with
  | none =>
    have secondSafe : (evaluate second middle).1 ≠ some .error := by
      rw [evaluate, fix_clock_evaluate, actual] at safe
      exact safe
    obtain ⟨middlePermutation, secondRun, secondCost⟩ := two middle actual finalPermutation secondSafe
    obtain ⟨initialPermutation, firstRun, firstCost⟩ := one middlePermutation firstSafe
    rw [actual] at firstRun
    refine ⟨initialPermutation, ?_, ?_⟩
    · rw [evaluate, fix_clock_evaluate, firstRun]
      rw [evaluate, fix_clock_evaluate, actual]
      exact secondRun
    · rw [wordFunctionExecutionCost_seq, wordFunctionExecutionCost_seq, firstRun, actual]
      simp only
      rw [firstCost, secondCost]
  | some result =>
    obtain ⟨initialPermutation, firstRun, firstCost⟩ := one finalPermutation firstSafe
    rw [actual] at firstRun
    refine ⟨initialPermutation, ?_, ?_⟩
    · rw [evaluate, fix_clock_evaluate, firstRun]
      rw [evaluate, fix_clock_evaluate, actual]
    · rw [wordFunctionExecutionCost_seq, wordFunctionExecutionCost_seq, firstRun, actual]
      simp only [Nat.add_zero]
      rw [firstCost]

/-- Only the actual selected arm is stitched; code/locals/operand values are
unaffected by changing the input permutation. -/
theorem function_permute_cost_ite {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (left : FunctionPermuteCostGoal price function first source) (right : FunctionPermuteCostGoal price function second source) :
    FunctionPermuteCostGoal price function (.ite cmp reg operand first second) source := by
  intro finalPermutation safe
  have gv : ∀ q : Nat → Nat → Nat, getVar reg {source with permute := q} = getVar reg source := fun _ => rfl
  have gi : ∀ q : Nat → Nat → Nat, getVarImm operand {source with permute := q} = getVarImm operand source := by
    intro q
    cases operand <;> rfl
  rw [evaluate] at safe
  rcases hx : getVar reg source with _ | x
  · simp only [hx] at safe
    exact (safe rfl).elim
  rcases hy : getVarImm operand source with _ | y
  · simp only [hx, hy] at safe
    exact (safe rfl).elim
  rcases comparison : wordSemWordCmp cmp x y with _ | selected
  · simp only [hx, hy, comparison] at safe
    exact (safe rfl).elim
  simp only [hx, hy, comparison] at safe
  cases selected with
  | false =>
    obtain ⟨initialPermutation, run, cost⟩ := right finalPermutation safe
    refine ⟨initialPermutation, ?_, ?_⟩
    · have sem : ∀ q, evaluate (.ite cmp reg operand first second) {source with permute := q} =
          evaluate second {source with permute := q} := by
        intro q
        rw [evaluate]
        simp only [gv, gi, hx, hy, comparison]
      have original : evaluate (.ite cmp reg operand first second) source = evaluate second source := by
        rw [evaluate]
        simp only [hx, hy, comparison]
      rw [sem, original]
      exact run
    · conv_lhs => rw [wordFunctionExecutionCost]
      conv_rhs => rw [wordFunctionExecutionCost]
      simp only [gv, gi, hx, hy, comparison]
      rw [cost]
  | true =>
    obtain ⟨initialPermutation, run, cost⟩ := left finalPermutation safe
    refine ⟨initialPermutation, ?_, ?_⟩
    · have sem : ∀ q, evaluate (.ite cmp reg operand first second) {source with permute := q} =
          evaluate first {source with permute := q} := by
        intro q
        rw [evaluate]
        simp only [gv, gi, hx, hy, comparison]
      have original : evaluate (.ite cmp reg operand first second) source = evaluate first source := by
        rw [evaluate]
        simp only [hx, hy, comparison]
      rw [sem, original]
      exact run
    · conv_lhs => rw [wordFunctionExecutionCost]
      conv_rhs => rw [wordFunctionExecutionCost]
      simp only [gv, gi, hx, hy, comparison]
      rw [cost]

/-- Termination scopes stitch their actual depth-decremented execution and
then restore the outer clock/depth, preserving the work of that body. -/
theorem function_permute_cost_mustTerminate {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (body : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (inner : source.termdep ≠ 0 → FunctionPermuteCostGoal price function body
      {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}) :
    FunctionPermuteCostGoal price function (.mustTerminate body) source := by
  intro finalPermutation safe
  by_cases zero : source.termdep = 0
  · rw [evaluate, dif_pos zero] at safe
    exact (safe rfl).elim
  let entry : WordSemStateFiniteExact 64 C F :=
    {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
  rcases actual : evaluate body entry with ⟨result, post⟩
  have sourceEq := WordToWord.evaluate_mustTerminate_run body source zero result post actual
  have noTimeout : result ≠ some .timeOut := by
    intro bad
    rw [sourceEq, if_pos bad] at safe
    exact (safe rfl).elim
  have bodySafe : (evaluate body entry).1 ≠ some .error := by
    rw [actual]
    rw [sourceEq, if_neg noTimeout] at safe
    exact safe
  obtain ⟨initialPermutation, bodyRun, cost⟩ := inner zero finalPermutation bodySafe
  rw [actual] at bodyRun
  have targetEntry : {{source with permute := initialPermutation} with
      clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1} =
      {entry with permute := initialPermutation} := rfl
  refine ⟨initialPermutation, ?_, ?_⟩
  · have targetRun : evaluate body {{source with permute := initialPermutation} with
        clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1} =
        (result, {post with permute := finalPermutation}) := by rw [targetEntry]; exact bodyRun
    have targetEq := WordToWord.evaluate_mustTerminate_run body {source with permute := initialPermutation}
      zero result _ targetRun
    rw [targetEq, sourceEq]
    simp only [if_neg noTimeout]
  · conv_lhs => rw [wordFunctionExecutionCost]
    conv_rhs => rw [wordFunctionExecutionCost]
    simp only [dif_neg zero]
    rw [targetEntry, cost]

#print axioms function_permute_cost_atomic
#print axioms function_permute_cost_seq
#print axioms function_permute_cost_ite
#print axioms function_permute_cost_mustTerminate
end InitECandidate.Runtime.FineCost
