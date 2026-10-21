import InitECandidate.Runtime.WordPostSSAReturnCost
import InitECandidate.Runtime.WordExecutionCostProps

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Transport unchanged caller syntax through the concrete optimized table.
The non-error guard is for the actual execution, including selected paths. -/
def PostSSATransportAt {C F : Type} (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F) : Prop :=
  (evaluate program source).1 ≠ some .error →
    evaluate program {source with code := postSSACodeTable source.code} =
      ((evaluate program source).1,
        {(evaluate program source).2 with code := postSSACodeTable source.code}) ∧
    wordExecutionCost wordOptimizerLocalPrice program
        {source with code := postSSACodeTable source.code} ≤
      wordExecutionCost wordOptimizerLocalPrice program source

/-- Source code constancy is essential here: the selected suffix must run
through the same optimized table as the reached prefix, rather than a table
silently remapped from a different state. -/
theorem postSSA_seq_transport {C F : Type} (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (firstFree : noInstallSubprogsHOL first = true) (codeFree : WordProps.noInstallCode source.code)
    (firstProof : PostSSATransportAt first source)
    (suffix : ∀ middle, evaluate first source = (none, middle) → PostSSATransportAt second middle) :
    PostSSATransportAt (.seq first second) source := by
  intro safe
  rcases actual : evaluate first source with ⟨result, middle⟩
  have firstSafe : (evaluate first source).1 ≠ some .error := by
    intro bad
    have error : result = some .error := by simpa only [actual] using bad
    rw [evaluate, fix_clock_evaluate, actual, error] at safe
    exact safe rfl
  obtain ⟨targetFirst, firstCost⟩ := firstProof firstSafe
  rw [actual] at targetFirst
  have middleCode : middle.code = source.code := by
    have h := code_evaluate first source firstFree codeFree
    simpa only [actual] using h
  cases result with
  | none =>
    have nextSafe : (evaluate second middle).1 ≠ some .error := by
      rw [evaluate, fix_clock_evaluate, actual] at safe
      exact safe
    obtain ⟨targetSecond, secondCost⟩ := suffix middle actual nextSafe
    rw [middleCode] at targetSecond secondCost
    constructor
    · rw [evaluate, fix_clock_evaluate, targetFirst]
      rw [evaluate, fix_clock_evaluate, actual]
      exact targetSecond
    · rw [wordExecutionCost_seq, wordExecutionCost_seq, targetFirst, actual]
      simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
        WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
      exact Nat.add_le_add firstCost secondCost
  | some outcome =>
    constructor
    · rw [evaluate, fix_clock_evaluate, targetFirst]
      rw [evaluate, fix_clock_evaluate, actual]
    · rw [wordExecutionCost_seq, wordExecutionCost_seq, targetFirst, actual]
      simpa only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
        WordToStack.refinedWordStackLeafBudget, Nat.zero_add, Nat.add_zero] using firstCost

/-- Only the selected conditional arm contributes work. Register and
immediate reads are unchanged by replacing the code table. -/
theorem postSSA_ite_transport {C F : Type} (cmp : Cmp) (reg : Nat)
    (operand : WordRegImm (BitVec 64)) (first second : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (left : PostSSATransportAt first source) (right : PostSSATransportAt second source) :
    PostSSATransportAt (.ite cmp reg operand first second) source := by
  intro safe
  let target : WordSemStateFiniteExact 64 C F := {source with code := postSSACodeTable source.code}
  have register : getVar reg target = getVar reg source := rfl
  have immediate : getVarImm operand target = getVarImm operand source := by cases operand <;> rfl
  change evaluate (.ite cmp reg operand first second) target = _ ∧
    wordExecutionCost wordOptimizerLocalPrice (.ite cmp reg operand first second) target ≤ _
  rw [evaluate] at safe
  rcases hx : getVar reg source with _ | x
  · simp only [hx] at safe
    exact (safe rfl).elim
  rcases hy : getVarImm operand source with _ | y
  · simp only [hx, hy] at safe
    exact (safe rfl).elim
  rcases compared : wordSemWordCmp cmp x y with _ | selected
  · simp only [hx, hy, compared] at safe
    exact (safe rfl).elim
  have selectedSafe := safe
  simp only [hx, hy, compared] at selectedSafe
  cases selected with
  | false =>
    obtain ⟨run, cost⟩ := right selectedSafe
    constructor
    · have semT : evaluate (.ite cmp reg operand first second) target = evaluate second target := by
        rw [evaluate]
        simp only [register, immediate, hx, hy, compared]
      have semS : evaluate (.ite cmp reg operand first second) source = evaluate second source := by
        rw [evaluate]
        simp only [hx, hy, compared]
      rw [semT, semS]
      exact run
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [register, immediate, hx, hy, compared, wordOptimizerLocalPrice,
        WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
      exact Nat.add_le_add_left cost 23
  | true =>
    obtain ⟨run, cost⟩ := left selectedSafe
    constructor
    · have semT : evaluate (.ite cmp reg operand first second) target = evaluate first target := by
        rw [evaluate]
        simp only [register, immediate, hx, hy, compared]
      have semS : evaluate (.ite cmp reg operand first second) source = evaluate first source := by
        rw [evaluate]
        simp only [hx, hy, compared]
      rw [semT, semS]
      exact run
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [register, immediate, hx, hy, compared, wordOptimizerLocalPrice,
        WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
      exact Nat.add_le_add_left cost 23

/-- MustTerminate charges the actual depth-decremented body; it does not
multiply work by its reset clock allowance. -/
theorem postSSA_mustTerminate_transport {C F : Type} (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (inner : source.termdep ≠ 0 → PostSSATransportAt body
      {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}) :
    PostSSATransportAt (.mustTerminate body) source := by
  intro safe
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
  obtain ⟨targetBody, cost⟩ := inner zero bodySafe
  rw [actual] at targetBody
  let target : WordSemStateFiniteExact 64 C F := {source with code := postSSACodeTable source.code}
  have targetEntry : {target with clock := wordSemMustTerminateLimit 64, termdep := target.termdep - 1} =
      {entry with code := postSSACodeTable entry.code} := rfl
  have targetRun : evaluate body
      {target with clock := wordSemMustTerminateLimit 64, termdep := target.termdep - 1} =
      (result, {post with code := postSSACodeTable source.code}) := by
    rw [targetEntry]
    exact targetBody
  constructor
  · have targetEq := WordToWord.evaluate_mustTerminate_run body target zero result _ targetRun
    change evaluate (.mustTerminate body) target = _
    rw [targetEq, sourceEq]
    simp only [if_neg noTimeout]
    rfl
  · change wordExecutionCost wordOptimizerLocalPrice (.mustTerminate body) target ≤ _
    rw [wordExecutionCost, wordExecutionCost]
    simp only [show target.termdep = source.termdep from rfl, dif_neg zero,
      wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
    rw [targetEntry]
    exact Nat.add_le_add_left cost _

#print axioms postSSA_seq_transport
#print axioms postSSA_ite_transport
#print axioms postSSA_mustTerminate_transport
end InitECandidate.Runtime.FineCost
