import InitECandidate.Runtime.WordFunctionPermuteExecutedCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Stitch the executed iterations backwards, preserving both the chosen
semantic permutation witness and its pure-node execution cost. -/
theorem function_permute_cost_loop {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → Nat) (function : Nat)
    (names exits : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 C F)
    (inner : ∀ cutSource, cutState (names, .ln) source = some cutSource →
      FunctionPermuteCostGoal price function body cutSource)
    (next : ∀ cutSource result middle,
      cutState (names, .ln) source = some cutSource →
      evaluate body cutSource = (result, middle) → wordSemContLoop result = true → middle.clock ≠ 0 →
      FunctionPermuteCostGoal price function (.loop names body exits) (decClock middle)) :
    FunctionPermuteCostGoal price function (.loop names body exits) source := by
  intro finalPermutation safe
  rcases cut : cutState (names, .ln) source with _ | cutSource
  · rw [evaluate, cut] at safe
    exact (safe rfl).elim
  rcases actual : evaluate body cutSource with ⟨result, middle⟩
  have bodySafe : (evaluate body cutSource).1 ≠ some .error := by
    intro bad
    have error : result = some .error := by simpa only [actual] using bad
    rw [evaluate, cut] at safe
    dsimp only at safe
    rw [fix_clock_evaluate, actual, error] at safe
    simpa [wordSemContLoop, wordSemExitLoop] using safe
  have targetCut : ∀ q : Nat → Nat → Nat,
      cutState (names, .ln) {source with permute := q} = some {cutSource with permute := q} := by
    intro q
    rw [cutState_withPermute, cut]
    rfl
  have sourceEq := WordToWord.evaluate_loop_run names exits body source cutSource cut result middle actual
  have sourceCost : wordFunctionExecutionCost (fun fn p _ => price fn p) function (.loop names body exits) source =
      price function (.loop names body exits) + wordFunctionExecutionCost (fun fn p _ => price fn p) function body cutSource +
        if wordSemContLoop result then
          (if middle.clock = 0 then 0 else wordFunctionExecutionCost (fun fn p _ => price fn p) function
            (.loop names body exits) (decClock middle)) else 0 := by
    rw [wordFunctionExecutionCost, cut]
    dsimp only
    rw [fix_clock_evaluate, actual]
    simp only [wordSemSTOP]
    split_ifs <;> rfl
  by_cases continuing : wordSemContLoop result = true
  · by_cases zero : middle.clock = 0
    · obtain ⟨initialPermutation, bodyRun, bodyCost⟩ := inner cutSource cut finalPermutation bodySafe
      rw [actual] at bodyRun
      refine ⟨initialPermutation, ?_, ?_⟩
      · have targetEq := WordToWord.evaluate_loop_run names exits body {source with permute := initialPermutation}
          {cutSource with permute := initialPermutation} (targetCut initialPermutation) result
          {middle with permute := finalPermutation} bodyRun
        rw [targetEq, sourceEq]
        simp [continuing, zero, flushState]
      · conv_lhs => rw [wordFunctionExecutionCost]
        rw [targetCut]
        dsimp only
        rw [fix_clock_evaluate, bodyRun, sourceCost]
        simp only [continuing, if_true, zero, bodyCost, dite_true, Nat.add_zero]
    · have nextSafe : (evaluate (.loop names body exits) (decClock middle)).1 ≠ some .error := by
        rw [sourceEq] at safe
        simpa only [continuing, if_true, zero, if_false, wordSemSTOP] using safe
      obtain ⟨middlePermutation, nextRun, nextCost⟩ :=
        next cutSource result middle cut actual continuing zero finalPermutation nextSafe
      obtain ⟨initialPermutation, bodyRun, bodyCost⟩ := inner cutSource cut middlePermutation bodySafe
      rw [actual] at bodyRun
      refine ⟨initialPermutation, ?_, ?_⟩
      · have targetEq := WordToWord.evaluate_loop_run names exits body {source with permute := initialPermutation}
          {cutSource with permute := initialPermutation} (targetCut initialPermutation) result
          {middle with permute := middlePermutation} bodyRun
        rw [targetEq, sourceEq]
        simp only [continuing, if_true, zero, if_false, wordSemSTOP]
        exact nextRun
      · conv_lhs => rw [wordFunctionExecutionCost]
        rw [targetCut]
        dsimp only
        rw [fix_clock_evaluate, bodyRun, sourceCost]
        simp only [continuing, if_true, zero, if_false, wordSemSTOP]
        rw [bodyCost]
        exact congrArg (fun n => price function (.loop names body exits) +
          wordFunctionExecutionCost (fun fn p _ => price fn p) function body cutSource + n) nextCost
  · obtain ⟨initialPermutation, bodyRun, bodyCost⟩ := inner cutSource cut finalPermutation bodySafe
    rw [actual] at bodyRun
    refine ⟨initialPermutation, ?_, ?_⟩
    · have targetEq := WordToWord.evaluate_loop_run names exits body {source with permute := initialPermutation}
        {cutSource with permute := initialPermutation} (targetCut initialPermutation) result
        {middle with permute := finalPermutation} bodyRun
      rw [targetEq, sourceEq]
      simp only [continuing, Bool.false_eq_true, if_false]
      rcases result with _ | result
      · simp [wordSemContLoop] at continuing
      cases result with
      | «break» n =>
          cases n with
          | zero =>
              simp only
              rw [cutState_withPermute]
              rcases exitCut : cutState (exits, .ln) middle with _ | post
              · rw [sourceEq] at safe
                simp [continuing, exitCut, wordSemExitLoop] at safe
              · rfl
          | succ n => simp [wordSemExitLoop]
      | _ => simp [wordSemExitLoop]
    · conv_lhs => rw [wordFunctionExecutionCost]
      rw [targetCut]
      dsimp only
      rw [fix_clock_evaluate, bodyRun, sourceCost]
      simp only [continuing, Bool.false_eq_true, if_false, bodyCost]

#print axioms function_permute_cost_loop
end InitECandidate.Runtime.FineCost
