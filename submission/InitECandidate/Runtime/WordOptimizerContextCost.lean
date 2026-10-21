import InitECandidate.Runtime.WordLoopCostCongruence
import InitECandidate.Runtime.WordCallContinuationCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

theorem optimizer_seq_prefix_run_eq {C F : Type}
    (first replacement suffix : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (same : evaluate replacement source = evaluate first source) :
    evaluate (.seq replacement suffix) source = evaluate (.seq first suffix) source := by
  rw [evaluate, evaluate, fix_clock_evaluate, fix_clock_evaluate, same]

theorem optimizer_seq_suffix_cost_le {C F : Type}
    (first suffix replacement : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (cheaper : ∀ middle, evaluate first source = (none, middle) →
      wordExecutionCost wordOptimizerLocalPrice replacement middle ≤
        wordExecutionCost wordOptimizerLocalPrice suffix middle) :
    wordExecutionCost wordOptimizerLocalPrice (.seq first replacement) source ≤
      wordExecutionCost wordOptimizerLocalPrice (.seq first suffix) source := by
  rw [wordExecutionCost_seq, wordExecutionCost_seq]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  rcases actual : evaluate first source with ⟨result, middle⟩
  cases result with
  | some outcome => exact Nat.le_refl _
  | none => exact Nat.add_le_add_left (cheaper middle actual) _

theorem optimizer_removeUnreach_run_eq {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate program source).1 ≠ some .error) :
    evaluate (WordUnreach.removeUnreach program) source = evaluate program source := by
  rcases actual : evaluate program source with ⟨result, post⟩
  exact WordUnreach.evaluateRemoveUnreach program source result post
    ⟨actual, by simpa only [actual] using safe⟩

theorem optimizer_seqAssocRight_run_eq {C F : Type}
    (program suffix : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.seq program suffix) source).1 ≠ some .error) :
    evaluate (WordUnreach.seqAssocRight program suffix) source = evaluate (.seq program suffix) source := by
  rcases actual : evaluate (.seq program suffix) source with ⟨result, post⟩
  exact WordUnreach.evaluateSeqAssocRightLemma program suffix source result post
    ⟨actual, by simpa only [actual] using safe⟩

theorem optimizer_seq_suffix_run_eq {C F : Type}
    (first suffix replacement : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (same : ∀ middle, evaluate first source = (none, middle) →
      evaluate replacement middle = evaluate suffix middle) :
    evaluate (.seq first replacement) source = evaluate (.seq first suffix) source := by
  rw [evaluate, evaluate, fix_clock_evaluate]
  rcases actual : evaluate first source with ⟨result, middle⟩
  cases result with
  | none => exact same middle actual
  | some outcome => rfl

/-- Put a normalized, cheaper prefix into its real suffix context and apply
the actual SimpSeq rewrite. Both intermediate semantic premises are derived. -/
theorem optimizer_normalized_context_cost_le {C F : Type}
    (program normalized suffix : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (normalForm : normalized = WordUnreach.removeUnreach program)
    (safe : (evaluate (.seq program suffix) source).1 ≠ some .error)
    (cheaper : wordExecutionCost wordOptimizerLocalPrice normalized source ≤
      wordExecutionCost wordOptimizerLocalPrice program source) :
    wordExecutionCost wordOptimizerLocalPrice (WordUnreach.simpSeq normalized suffix) source ≤
      wordExecutionCost wordOptimizerLocalPrice (.seq program suffix) source := by
  have same : evaluate normalized source = evaluate program source := by
    rw [normalForm]
    exact optimizer_removeUnreach_run_eq program source (optimizer_seq_prefix_safe program suffix source safe)
  have sameSeq := optimizer_seq_prefix_run_eq program normalized suffix source same
  exact (optimizer_simpSeq_cost_le normalized suffix source (sameSeq.symm ▸ safe)).trans
    (optimizer_seq_prefix_cost_le program normalized suffix source same cheaper)

/-- Actual selected-arm congruence, with child bounds needed only when that
child's evaluation is non-error. -/
theorem optimizer_if_body_cost_le {C F : Type}
    (cmp : Compiler.Encoders.Asm.HolCmp) (register : Nat) (operand : WordRegImm (BitVec 64))
    (first second replacementFirst replacementSecond : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.ite cmp register operand first second) source).1 ≠ some .error)
    (yes : (evaluate first source).1 ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice replacementFirst source ≤
        wordExecutionCost wordOptimizerLocalPrice first source)
    (no : (evaluate second source).1 ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice replacementSecond source ≤
        wordExecutionCost wordOptimizerLocalPrice second source) :
    wordExecutionCost wordOptimizerLocalPrice
      (.ite cmp register operand replacementFirst replacementSecond) source ≤
      wordExecutionCost wordOptimizerLocalPrice (.ite cmp register operand first second) source := by
  rw [wordExecutionCost, wordExecutionCost]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget]
  cases left : getVar register source with
  | none => simp only [left, Nat.le_refl]
  | some x =>
    cases right : getVarImm operand source with
    | none => simp only [left, right, Nat.le_refl]
    | some y =>
      cases compared : wordSemWordCmp cmp x y with
      | none => simp only [left, right, compared, Nat.le_refl]
      | some selected =>
        rw [evaluate, left, right] at safe
        cases selected
        · have childSafe : (evaluate second source).1 ≠ some .error := by
            simpa only [compared] using safe
          simpa only [left, right, compared] using Nat.add_le_add_left (no childSafe) 23
        · have childSafe : (evaluate first source).1 ≠ some .error := by
            simpa only [compared] using safe
          simpa only [left, right, compared] using Nat.add_le_add_left (yes childSafe) 23

theorem optimizer_mustTerminate_body_cost_le {C F : Type}
    (body replacement : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate (.mustTerminate body) source).1 ≠ some .error)
    (cheaper : ∀ child : WordSemStateFiniteExact 64 C F,
      (evaluate body child).1 ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice replacement child ≤
        wordExecutionCost wordOptimizerLocalPrice body child) :
    wordExecutionCost wordOptimizerLocalPrice (.mustTerminate replacement) source ≤
      wordExecutionCost wordOptimizerLocalPrice (.mustTerminate body) source := by
  rw [wordExecutionCost, wordExecutionCost]
  simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
    WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
  by_cases zero : source.termdep = 0
  · simp only [zero, dif_pos, Nat.le_refl]
  · simp only [zero, if_false]
    apply cheaper
    intro bad
    rcases actual : evaluate body
        {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1} with ⟨result, post⟩
    have error : result = some .error := by simpa only [actual] using bad
    rw [evaluate, dif_neg zero, actual, error] at safe
    simpa using safe

#print axioms optimizer_normalized_context_cost_le
#print axioms optimizer_if_body_cost_le
#print axioms optimizer_mustTerminate_body_cost_le

/-- A tail call never falls through, even if its callee returns an invalid
ordinary result: that becomes an error rather than executing the suffix. -/
theorem optimizer_tail_call_stops {C F : Type}
    (destination : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 C F) :
    (evaluate (.call none destination arguments handler) source).1.isSome = true := by
  have clause := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [clause]
  cases foundArgs : getVars arguments source with
  | none => rfl
  | some xs =>
    simp only
    by_cases bad : wordSemBadDestArgs destination arguments = true
    · rw [if_pos bad]; rfl
    rw [if_neg bad]
    cases found : wordSemFindCode destination (wordSemAddRetLoc
        (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat)) xs)
        source.code source.stackSize with
    | none => rfl
    | some data =>
      rcases data with ⟨actualArgs, body, size⟩
      simp only
      cases handler with
      | some _ => rfl
      | none =>
        simp only
        by_cases zero : source.clock = 0
        · rw [if_pos zero]; rfl
        rw [if_neg zero]
        rcases evaluate body (callEnv actualArgs size (decClock source)) with ⟨result, post⟩
        simp only
        by_cases badReturn : wordSemBadFunReturn result = true
        · rw [if_pos badReturn]; rfl
        · rw [if_neg badReturn]
          cases result with
          | none => simp [wordSemBadFunReturn] at badReturn
          | some _ => rfl

#print axioms optimizer_tail_call_stops
end InitECandidate.Runtime.FineCost
