import InitECandidate.Runtime.WordCopyAtomicCost
import Flapjack.Compiler.Backend.WordCopy.Proofs.Correct

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Whole local copy-propagation work transfer. The current code table is
unchanged; aliases are justified by the pinned semantic invariant. -/
theorem copyProp_executed_cost_le {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (aliases : WordCopy.CopyState) (invariant : WordCopy.cpStateInv aliases)
    (models : WordCopy.cpStateModels aliases source)
    (safe : (evaluate program source).1 ≠ some .error) :
    wordExecutionCost wordOptimizerLocalPrice (WordCopy.copyPropProg program aliases).1 source ≤
      wordExecutionCost wordOptimizerLocalPrice program source := by
  cases program
  case seq first second =>
    rcases compiledFirst : WordCopy.copyPropProg first aliases with ⟨first', nextAliases⟩
    rcases compiledSecond : WordCopy.copyPropProg second nextAliases with ⟨second', finalAliases⟩
    have prefixSafe : (evaluate first source).1 ≠ some .error := by
      intro bad
      rcases actual : evaluate first source with ⟨result, middle⟩
      have error : result = some .error := by simpa only [actual] using bad
      rw [evaluate, fix_clock_evaluate, actual, error] at safe
      exact safe rfl
    have firstCost := copyProp_executed_cost_le first source aliases invariant models prefixSafe
    rw [compiledFirst] at firstCost
    rcases actual : evaluate first source with ⟨result, middle⟩
    have notError : result ≠ some .error := by simpa only [actual] using prefixSafe
    obtain ⟨targetRun, nextModels⟩ := WordCopy.copyPropCorrect first aliases source
      first' nextAliases result middle ⟨invariant, models, compiledFirst, notError, actual⟩
    simp only [WordCopy.copyPropProg, compiledFirst, compiledSecond]
    rw [wordExecutionCost_seq, wordExecutionCost_seq, actual, targetRun]
    simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
    cases result with
    | some outcome => exact Nat.add_le_add_right firstCost 0
    | none =>
      have nextSafe : (evaluate second middle).1 ≠ some .error := by
        rw [evaluate, fix_clock_evaluate, actual] at safe
        exact safe
      have clock := evaluate_clock first source none middle actual
      have secondCost := copyProp_executed_cost_le second middle nextAliases
        (WordCopy.copyPropProgInv ⟨invariant, compiledFirst⟩) (nextModels rfl) nextSafe
      rw [compiledSecond] at secondCost
      exact Nat.add_le_add firstCost secondCost
  case ite cmp register operand first second =>
    simp only [WordCopy.copyPropProg]
    rw [wordExecutionCost, wordExecutionCost]
    simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
    rw [WordCopy.cpStateModelsDGetVar ⟨invariant, models⟩,
      WordCopy.cpStateModelsDGetVarImm ⟨invariant, models⟩]
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
              (copyProp_executed_cost_le second source aliases invariant models nextSafe) 23
          · have nextSafe : (evaluate first source).1 ≠ some .error := by
              rw [evaluate, left, right] at safe
              simpa only [compared] using safe
            simpa only [left, right, compared] using Nat.add_le_add_left
              (copyProp_executed_cost_le first source aliases invariant models nextSafe) 23
  case loop names body exits =>
    rcases compiled : WordCopy.copyPropProg body WordCopy.emptyEq with ⟨body', bodyAliases⟩
    simp only [WordCopy.copyPropProg, compiled]
    rw [wordExecutionCost, wordExecutionCost]
    simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
    cases cut : cutState (names, .ln) source with
    | none => simp only [cut, Nat.le_refl]
    | some cutSource =>
      rcases actual : evaluate body cutSource with ⟨result, middle⟩
      have bodySafe : (evaluate body cutSource).1 ≠ some .error := by
        intro bad
        have error : result = some .error := by simpa only [actual] using bad
        rw [evaluate, cut] at safe
        dsimp only at safe
        rw [fix_clock_evaluate, actual, error] at safe
        simpa [wordSemContLoop, wordSemExitLoop] using safe
      have notError : result ≠ some .error := by simpa only [actual] using bodySafe
      have targetRun := (WordCopy.copyPropCorrect body WordCopy.emptyEq cutSource
        body' bodyAliases result middle
        ⟨WordCopy.emptyEqInv, WordCopy.emptyEqModel, compiled, notError, actual⟩).1
      have cutClock := cutState_clock_termdep (names, .ln) source cutSource cut
      have bodyCost := copyProp_executed_cost_le body cutSource WordCopy.emptyEq
        WordCopy.emptyEqInv WordCopy.emptyEqModel bodySafe
      rw [compiled] at bodyCost
      simp only [cut, fix_clock_evaluate, actual, targetRun]
      have fixed : fixClock cutSource (result, middle) = (result, middle) := by
        rw [← actual, fix_clock_evaluate]
      rw [fixed]
      by_cases continuing : wordSemContLoop result = true
      · simp only [continuing, if_true]
        by_cases zero : middle.clock = 0
        · simp only [zero, if_true, Nat.add_zero]
          exact Nat.add_le_add_left bodyCost 2
        · simp only [zero, if_false, wordSemSTOP]
          have nextSafe : (evaluate (.loop names body exits) (decClock middle)).1 ≠ some .error := by
            rw [evaluate, cut] at safe
            dsimp only at safe
            rw [fix_clock_evaluate, actual] at safe
            simpa [continuing, zero, wordSemSTOP] using safe
          have clock := evaluate_clock body cutSource result middle actual
          have nextCost := copyProp_executed_cost_le (.loop names body exits) (decClock middle)
            WordCopy.emptyEq WordCopy.emptyEqInv WordCopy.emptyEqModel nextSafe
          simp only [WordCopy.copyPropProg, compiled] at nextCost
          exact Nat.add_le_add (Nat.add_le_add_left bodyCost 2) nextCost
      · simp only [continuing, if_false, Nat.add_zero]
        exact Nat.add_le_add_left bodyCost 2
  case mustTerminate body =>
    simp only [WordCopy.copyPropProg]
    rw [wordExecutionCost, wordExecutionCost]
    simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, Nat.zero_add]
    by_cases zero : source.termdep = 0
    · simp only [zero, dif_pos, Nat.le_refl]
    · simp only [zero, if_false]
      let next : WordSemStateFiniteExact 64 C F :=
        {source with clock := wordSemMustTerminateLimit 64, termdep := source.termdep - 1}
      have bodySafe : (evaluate body next).1 ≠ some .error := by
        intro bad
        rcases actual : evaluate body next with ⟨result, middle⟩
        have error : result = some .error := by simpa only [actual] using bad
        rw [evaluate, dif_neg zero, actual, error] at safe
        simpa using safe
      exact copyProp_executed_cost_le body next aliases invariant
        (WordCopy.cpStateModelsSame ⟨models, rfl, rfl⟩) bodySafe
  case call returns destination arguments handler => exact Nat.le_refl _
  all_goals exact copyProp_atomic_executed_cost_le _ aliases source rfl
termination_by (source.termdep, source.clock, sizeOf program)
decreasing_by
  all_goals simp_wf
  all_goals simp_all [Prod.lex_def, decClock]
  all_goals omega

#print axioms copyProp_executed_cost_le

/-- Public copy-propagation endpoint: the pinned semantic run is reproduced
with a nonincreasing executed cost, starting from discharged empty aliases. -/
theorem copyProp_executed_correct {C F : Type}
    (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (safe : (evaluate program source).1 ≠ some .error) :
    evaluate (WordCopy.copyProp program) source = evaluate program source ∧
      wordExecutionCost wordOptimizerLocalPrice (WordCopy.copyProp program) source ≤
        wordExecutionCost wordOptimizerLocalPrice program source := by
  exact ⟨WordCopy.evaluateCopyProp safe,
    copyProp_executed_cost_le program source WordCopy.emptyEq
      WordCopy.emptyEqInv WordCopy.emptyEqModel safe⟩

#print axioms copyProp_executed_correct
end InitECandidate.Runtime.FineCost
