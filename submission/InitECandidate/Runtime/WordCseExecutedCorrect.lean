import InitECandidate.Runtime.WordCseExecutedLoop
import InitECandidate.Runtime.WordCseAtomicCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Whole local CSE pass: the actual transformed execution costs no more
than its flat, non-error source execution. Calls use the same code table in
this theorem; whole-table transformation is a separate global composition. -/
theorem cse_executed_cost_le {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (data : WordCse.Knowledge) (flat : flatExpConventions program = true)
    (valid : WordCse.dataInv data source) (safe : (evaluate program source).1 ≠ some .error) :
    wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCse data program).2 source ≤
      wordExecutionCost wordOptimizerLocalPrice program source := by
  cases program
  case seq first second =>
    have parts : flatExpConventions first = true ∧ flatExpConventions second = true := by
      simpa only [flatExpConventions, Bool.and_eq_true] using flat
    have prefixSafe : (evaluate first source).1 ≠ some .error := by
      intro bad
      rcases actual : evaluate first source with ⟨result, middle⟩
      have error : result = some .error := by simpa only [actual] using bad
      rw [evaluate, fix_clock_evaluate, actual, error] at safe
      exact safe rfl
    apply cse_seq_executed_cost_le data first second source parts.1 valid prefixSafe
    · exact cse_executed_cost_le first source data parts.1 valid prefixSafe
    · intro middle actual nextValid
      have nextSafe : (evaluate second middle).1 ≠ some .error := by
        rw [evaluate, fix_clock_evaluate, actual] at safe
        exact safe
      have clock := evaluate_clock first source none middle actual
      exact cse_executed_cost_le second middle _ parts.2 nextValid nextSafe
  case ite cmp register operand first second =>
    have parts : flatExpConventions first = true ∧ flatExpConventions second = true := by
      simpa only [flatExpConventions, Bool.and_eq_true] using flat
    simp only [WordCse.wordCse]
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
          cases selected
          · have nextSafe : (evaluate second source).1 ≠ some .error := by
              rw [evaluate, left, right] at safe
              simpa only [compared] using safe
            simpa only [left, right, compared] using Nat.add_le_add_left
              (cse_executed_cost_le second source data parts.2 valid nextSafe) 23
          · have nextSafe : (evaluate first source).1 ≠ some .error := by
              rw [evaluate, left, right] at safe
              simpa only [compared] using safe
            simpa only [left, right, compared] using Nat.add_le_add_left
              (cse_executed_cost_le first source data parts.1 valid nextSafe) 23
  case loop names body exits =>
    have bodyFlat : flatExpConventions body = true := flat
    have bodySafe : ∀ cutSource, cutState (names, .ln) source = some cutSource →
        (evaluate body cutSource).1 ≠ some .error := by
      intro cutSource cut bad
      rcases actual : evaluate body cutSource with ⟨result, middle⟩
      have error : result = some .error := by simpa only [actual] using bad
      rw [evaluate, cut] at safe
      dsimp only at safe
      rw [fix_clock_evaluate, actual, error] at safe
      simpa [wordSemContLoop, wordSemExitLoop] using safe
    apply cse_loop_executed_cost_le data names exits body source bodyFlat bodySafe
    · intro cutSource cut
      have clock := cutState_clock_termdep (names, .ln) source cutSource cut
      exact cse_executed_cost_le body cutSource WordCse.emptyData bodyFlat
        (WordCse.dataInvEmpty cutSource) (bodySafe cutSource cut)
    · intro cutSource result middle cut actual continuing positive
      have nextSafe : (evaluate (.loop names body exits) (decClock middle)).1 ≠ some .error := by
        rw [evaluate, cut] at safe
        dsimp only at safe
        rw [fix_clock_evaluate, actual] at safe
        simpa [continuing, positive, wordSemSTOP] using safe
      have clock := evaluate_clock body cutSource result middle actual
      have cutClock := cutState_clock_termdep (names, .ln) source cutSource cut
      have next := cse_executed_cost_le (.loop names body exits) (decClock middle)
        WordCse.emptyData flat (WordCse.dataInvEmpty _) nextSafe
      simpa only [WordCse.wordCse] using next
  case mustTerminate body =>
    have bodyFlat : flatExpConventions body = true := flat
    apply cse_mustTerminate_executed_cost_le
    intro positive
    let next : WordSemStateFiniteExact 64 C F :=
      {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
    have bodySafe : (evaluate body next).1 ≠ some .error := by
      intro bad
      rcases actual : evaluate body next with ⟨result, middle⟩
      have error : result = some .error := by simpa only [actual] using bad
      rw [evaluate, dif_neg positive] at safe
      rw [actual, error] at safe
      simpa using safe
    exact cse_executed_cost_le body next data bodyFlat
      (WordCse.data_inv_clock data source _ _ valid) bodySafe
  case call returns destination arguments handler =>
    exact le_of_eq (cse_call_executed_cost_eq data returns destination arguments handler source)
  all_goals exact cse_atomic_executed_cost_le data _ source rfl
termination_by (source.termdep, source.clock, sizeOf program)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, decClock]
  all_goals omega

#print axioms cse_executed_cost_le

/-- Actual whole-pass semantic and quantitative endpoint for CSE, with the
empty knowledge discharged. This theorem concerns the current code table;
it supplies the local transformation half of a global code-table proof. -/
theorem word_common_subexp_elim_executed_correct {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source post : WordSemStateFiniteExact 64 C F)
    (result : Option (WordSemResult 64))
    (run : evaluate program source = (result, post))
    (flat : flatExpConventions program = true) (safe : result ≠ some .error) :
    evaluate (WordCse.wordCommonSubexpElim program) source = (result, post) ∧
      wordExecutionCost wordOptimizerLocalPrice (WordCse.wordCommonSubexpElim program) source ≤
        wordExecutionCost wordOptimizerLocalPrice program source := by
  refine ⟨WordCse.word_common_subexp_elim_correct program source result post ⟨run, flat, safe⟩, ?_⟩
  exact cse_executed_cost_le program source WordCse.emptyData flat
    (WordCse.dataInvEmpty source) (by simpa only [run] using safe)

#print axioms word_common_subexp_elim_executed_correct
end InitECandidate.Runtime.FineCost
