import InitECandidate.Runtime.RawCallReturningCost

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack.Compiler.Backend.StackRawCall.CallCase
open InitECandidate.Runtime.StackToLab

/-- Returning-call compiler simulation charges the actual callee and only its
selected normal or exception continuation, preserving the original relation
and both resource exceptions. No compiled run or whole target budget is assumed. -/
theorem executed_returning {F : Type} (bounds : BitVec 64 × BitVec 64)
    (ret : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg 64 × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (calleeIH : ExecutedReturnCalleeIH (refinedRemovalLocalPrice 6 bounds) dest link l1 l2 source)
    (returnIH : ExecutedReturnContinuationIH (refinedRemovalLocalPrice 6 bounds) ret dest link l1 l2 source)
    (exceptionIH : ExecutedExceptionContinuationIH (refinedRemovalLocalPrice 6 bounds) handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds)
      (comp info (.call (some (ret, link, l1, l2)) dest handler)) info target post result
      (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
        (.call (some (ret, link, l1, l2)) dest handler) source) := by
  classical
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rw [StackSemEvaluate.evaluate_call] at execution
  dsimp only at execution
  cases lookup : findCode dest (source.regs.eraseEq link) source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      have clockEq := LoopCase.stateRel_clock info source target relation
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨entryInfo, _, targetLookup⟩ :=
          callEntryErased info source target relation dest link program lookup
        refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
          LoopCase.stateRel_emptyEnv info source target relation, ?_, by simp, ?_⟩
        · have targetZero : target.clock = 0 := clockEq.trans zero
          have update : {target with clock := 0} = target := by rw [← targetZero]
          cases handler with
          | none =>
              simp only [comp, Nat.add_zero, targetZero, update,
                StackSemEvaluate.evaluate_call, targetLookup, if_true]
          | some triple =>
              obtain ⟨h, hl1, hl2⟩ := triple
              simp only [comp, Nat.add_zero, targetZero, update,
                StackSemEvaluate.evaluate_call, targetLookup, if_true]
        · rcases handler with _ | ⟨hp, hs, hl⟩
          all_goals
            try simp only [comp]
            conv_lhs => rw [stackExecutionCost]
            conv_rhs => rw [stackExecutionCost]
            simp [zero, clockEq, refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap]
      · simp only [zero, if_false] at execution
        rw [StackSemEvaluateClock.fixClockEvaluate] at execution
        rcases bodyExecution : StackSemEvaluate.evaluate
          (program, decClock (setVar link (.loc l1 l2) source)) with
          ⟨bodyResult, middle⟩
        rw [bodyExecution] at execution
        have bodyNonerror : bodyResult ≠ some .error := by
          intro equal
          rw [equal] at execution
          simp only [Prod.mk.injEq] at execution
          exact nonerror execution.1.symm
        obtain ⟨entryInfo, targetLookup, firstClock, targetMiddle, firstSpace,
          middleRelation, calleeExecution, firstGuard, firstCost⟩ :=
          executed_returning_callee (refinedRemovalLocalPrice 6 bounds) dest link l1 l2 info source target middle program bodyResult
            calleeIH relation lookup zero bodyExecution bodyNonerror
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + firstClock ≠ 0 := by omega
        have calleeNative : StackSemEvaluate.evaluate
            (compTop entryInfo program, decClock (setVar link (.loc l1 l2)
              {target with clock := target.clock + firstClock})) =
            (bodyResult, {targetMiddle with stackSpace := firstSpace}) := by
          rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
          exact calleeExecution
        cases bodyResult with
        | none =>
            simp only [Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
        | some value =>
            cases value with
            | error => exact False.elim (bodyNonerror rfl)
            | «break» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | «continue» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | halt value =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard, ?_⟩
                · cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                · rcases handler with _ | ⟨hp, hs, hl⟩
                  all_goals
                    try simp only [comp]
                    rw [returning_executionCost_eq (source := {target with clock := target.clock + firstClock}) (lookup := targetLookup) (nonzero := addedNonzero) (bodyRun := calleeNative),
                      returning_executionCost_eq (source := source) (lookup := lookup) (nonzero := zero) (bodyRun := bodyExecution)]
                    simp only [selectedContinuationBudget, Nat.add_zero]
                    rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                    simpa only [refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap] using
                      Nat.add_le_add_right firstCost (10 + callJumpWork dest)
            | timeOut =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard, ?_⟩
                · cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                · rcases handler with _ | ⟨hp, hs, hl⟩
                  all_goals
                    try simp only [comp]
                    rw [returning_executionCost_eq (source := {target with clock := target.clock + firstClock}) (lookup := targetLookup) (nonzero := addedNonzero) (bodyRun := calleeNative),
                      returning_executionCost_eq (source := source) (lookup := lookup) (nonzero := zero) (bodyRun := bodyExecution)]
                    simp only [selectedContinuationBudget, Nat.add_zero]
                    rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                    simpa only [refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap] using
                      Nat.add_le_add_right firstCost (10 + callJumpWork dest)
            | finalFFI event =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard, ?_⟩
                · cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                · rcases handler with _ | ⟨hp, hs, hl⟩
                  all_goals
                    try simp only [comp]
                    rw [returning_executionCost_eq (source := {target with clock := target.clock + firstClock}) (lookup := targetLookup) (nonzero := addedNonzero) (bodyRun := calleeNative),
                      returning_executionCost_eq (source := source) (lookup := lookup) (nonzero := zero) (bodyRun := bodyExecution)]
                    simp only [selectedContinuationBudget, Nat.add_zero]
                    rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                    simpa only [refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap] using
                      Nat.add_le_add_right firstCost (10 + callJumpWork dest)
            | result value =>
                by_cases equal : value = .loc l1 l2
                · subst value
                  simp only [ne_eq, not_true_eq_false, if_false] at execution
                  have spaceEq := firstGuard (by simp)
                  subst firstSpace
                  have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                      targetMiddle := by cases targetMiddle; rfl
                  rw [selfSpace] at calleeExecution
                  obtain ⟨secondClock, targetPost, finalSpace, postRelation,
                    continuationExecution, finalGuard, secondCost⟩ :=
                    returnIH program lookup zero middle bodyExecution info targetMiddle post result
                      ⟨execution, nonerror, middleRelation⟩
                  have extended := extendReturningCallee (compTop entryInfo program) target
                    targetMiddle (some (.result (.loc l1 l2))) link l1 l2 firstClock secondClock
                    targetNonzero calleeExecution (by simp)
                  have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                  refine ⟨firstClock + secondClock, targetPost, finalSpace, postRelation, ?_, finalGuard, ?_⟩
                  · cases handler with
                    | none =>
                        simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                          totalNonzero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                        simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                    | some triple =>
                        obtain ⟨h, hl1, hl2⟩ := triple
                        simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                          totalNonzero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                        simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                  · rcases handler with _ | ⟨hp, hs, hl⟩
                    all_goals
                      try simp only [comp]
                      rw [returning_executionCost_eq (source := {target with clock := target.clock + (firstClock + secondClock)}) (lookup := targetLookup) (nonzero := totalNonzero) (bodyRun := extended),
                        returning_executionCost_eq (source := source) (lookup := lookup) (nonzero := zero) (bodyRun := bodyExecution)]
                      simp only [selectedContinuationBudget, ↓reduceIte]
                      have stable := stackExecutionCost_addClock (refinedRemovalLocalPrice 6 bounds)
                        (compTop entryInfo program)
                        {decClock (setVar link (.loc l1 l2) target) with
                          clock := (decClock (setVar link (.loc l1 l2) target)).clock + firstClock}
                        targetMiddle _ calleeExecution (by simp) secondClock
                      rw [returningInput_addClock target link l1 l2 (firstClock + secondClock) targetNonzero]
                      simp only [Nat.add_assoc] at stable
                      rw [stable]
                      simpa only [refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap] using
                        Nat.add_le_add_right (Nat.add_le_add firstCost secondCost) (10 + callJumpWork dest)
                · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                  exact False.elim (nonerror execution.1.symm)
            | exception value =>
                cases handler with
                | none =>
                    simp only [Prod.mk.injEq] at execution
                    obtain ⟨rfl, rfl⟩ := execution
                    refine ⟨firstClock, targetMiddle, firstSpace, middleRelation, ?_, firstGuard, ?_⟩
                    · simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        addedNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                    ·
                      all_goals
                        try simp only [comp]
                        rw [returning_executionCost_eq (source := {target with clock := target.clock + firstClock}) (lookup := targetLookup) (nonzero := addedNonzero) (bodyRun := calleeNative),
                          returning_executionCost_eq (source := source) (lookup := lookup) (nonzero := zero) (bodyRun := bodyExecution)]
                        simp only [selectedContinuationBudget, Nat.add_zero]
                        rw [returningInput_addClock target link l1 l2 firstClock targetNonzero]
                        simpa only [refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap] using
                          Nat.add_le_add_right firstCost (10 + callJumpWork dest)
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    by_cases equal : value = .loc hl1 hl2
                    · subst value
                      simp only [ne_eq, not_true_eq_false, if_false] at execution
                      have spaceEq := firstGuard (by simp)
                      subst firstSpace
                      have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                          targetMiddle := by cases targetMiddle; rfl
                      rw [selfSpace] at calleeExecution
                      obtain ⟨secondClock, targetPost, finalSpace, postRelation,
                        continuationExecution, finalGuard, secondCost⟩ :=
                        exceptionIH program h hl1 hl2 lookup zero rfl middle bodyExecution
                          info targetMiddle post result ⟨execution, nonerror, middleRelation⟩
                      have extended := extendReturningCallee (compTop entryInfo program) target
                        targetMiddle (some (.exception (.loc hl1 hl2))) link l1 l2
                        firstClock secondClock targetNonzero calleeExecution (by simp)
                      have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                      refine ⟨firstClock + secondClock, targetPost, finalSpace,
                        postRelation, ?_, finalGuard, ?_⟩
                      · simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                          totalNonzero, if_false]
                        rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                        simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                      ·
                        all_goals
                          try simp only [comp]
                          rw [returning_executionCost_eq (source := {target with clock := target.clock + (firstClock + secondClock)}) (lookup := targetLookup) (nonzero := totalNonzero) (bodyRun := extended),
                            returning_executionCost_eq (source := source) (lookup := lookup) (nonzero := zero) (bodyRun := bodyExecution)]
                          simp only [selectedContinuationBudget, ↓reduceIte]
                          have stable := stackExecutionCost_addClock (refinedRemovalLocalPrice 6 bounds)
                            (compTop entryInfo program)
                            {decClock (setVar link (.loc l1 l2) target) with
                              clock := (decClock (setVar link (.loc l1 l2) target)).clock + firstClock}
                            targetMiddle _ calleeExecution (by simp) secondClock
                          rw [returningInput_addClock target link l1 l2 (firstClock + secondClock) targetNonzero]
                          simp only [Nat.add_assoc] at stable
                          rw [stable]
                          simpa only [refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap] using
                            Nat.add_le_add_right (Nat.add_le_add firstCost secondCost) (10 + callJumpWork dest)
                    · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                      exact False.elim (nonerror execution.1.symm)

#print axioms executed_returning
end InitECandidate.Runtime.StackRawCall
