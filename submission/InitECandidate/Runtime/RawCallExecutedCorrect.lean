import InitECandidate.Runtime.RawCallExecutedJump
import InitECandidate.Runtime.StackExecutionCompleteTail

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.StackSemMeasure
open InitECandidate.Runtime.StackToLab

private theorem rawCost_smaller {F : Type} (p q : HolProg 64)
    (source child : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (clock : child.clock ≤ source.clock) (size : sizeOf q < sizeOf p) :
    LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) := by
  rcases Nat.lt_or_eq_of_le clock with lt | eq
  · exact Prod.Lex.left _ _ lt
  · rw [eq]; exact Prod.Lex.right _ size

/-- Whole raw-call compiler execution-cost transfer, with coefficient one.
The only cost assumptions are finite static frame eligibility. Recursive
simulations and target budgets are derived by the actual execution measure;
the closed oracle preserves code eligibility across reached executions. -/
theorem rawCall_cost_correct {F : Type} (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : rawCallFramesSupported p = true)
    (global : RawCallFramesSupportedCode source.code) (oracle : EmptyInstallOracle source) :
    ∀ info target post result,
      StackSemEvaluate.evaluate (p, source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info source target →
      ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds) (compTop info p)
        info target post result (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) p source) ∧
      ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds) (comp info p)
        info target post result (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) p source) := by
  have ih : ∀ q (child : StackSemStateFiniteExact 64 LabToTarget.Config F),
      LexNat (child.clock, sizeOf q) (source.clock, sizeOf p) →
      rawCallFramesSupported q = true → RawCallFramesSupportedCode child.code →
      EmptyInstallOracle child → ∀ info target post result,
      StackSemEvaluate.evaluate (q, child) = (result, post) ∧
        result ≠ some .error ∧ stateRel info child target →
      ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds) (compTop info q)
        info target post result (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) q child) ∧
      ExecutedSimulationResult (refinedRemovalLocalPrice 6 bounds) (comp info q)
        info target post result (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) q child) := by
    intro q child smaller eligible code closed
    exact rawCall_cost_correct bounds q child eligible code closed
  intro info target post result hypothesis
  by_cases atomic : rawCostAtomic p = true
  · exact executed_atomic (refinedRemovalLocalPrice 6 bounds) p info source target post result atomic hypothesis
  cases p <;> try (solve | simp [rawCostAtomic] at atomic)
  case seq first second =>
    have pair : rawCallFramesSupported first = true ∧ rawCallFramesSupported second = true := by
      simpa only [rawCallFramesSupported, Bool.and_eq_true] using supported
    apply executed_seq bounds first second info source target post result supported global
    · intro i t out r h
      exact (ih first source (Prod.Lex.right _ (by simp; omega)) pair.1 global oracle i t out r h).2
    · intro middle firstRun i t out r h
      obtain ⟨code, closed⟩ := RawCallFramesSupportedCode.after_evaluate first source middle none oracle global firstRun
      exact (ih second middle (rawCost_smaller _ _ source middle
        (StackSemEvaluateClock.evaluateClock first source none middle firstRun) (by simp))
        pair.2 code closed i t out r h).2
    · exact hypothesis
  case ite cmp reg operand yes no =>
    have pair : rawCallFramesSupported yes = true ∧ rawCallFramesSupported no = true := by
      simpa only [rawCallFramesSupported, Bool.and_eq_true] using supported
    have sim := executed_if (refinedRemovalLocalPrice 6 bounds) cmp reg operand yes no info
      (by rfl) source target post result
      (fun _ _ _ _ _ i t out r h =>
        (ih yes source (Prod.Lex.right _ (by simp; omega)) pair.1 global oracle i t out r h).2)
      (fun _ _ _ _ _ i t out r h =>
        (ih no source (Prod.Lex.right _ (by simp)) pair.2 global oracle i t out r h).2) hypothesis
    exact ⟨by simpa only [compTop] using sim, sim⟩
  case loop body =>
    have bodySupported : rawCallFramesSupported body = true := by
      simpa only [rawCallFramesSupported] using supported
    have bodyIH : ExecutedProgramIH (refinedRemovalLocalPrice 6 bounds) body source := by
      intro i t out r h
      exact (ih body source (Prod.Lex.right _ (by simp)) bodySupported global oracle i t out r h).2
    have reentryIH : ExecutedLoopReentryIH (refinedRemovalLocalPrice 6 bounds) body source := by
      intro bodyResult middle bodyRun continues positive i t out r h
      obtain ⟨code, closed⟩ := RawCallFramesSupportedCode.after_evaluate body source middle bodyResult oracle global bodyRun
      have lower := LoopCase.loopReentryClockLess body source middle bodyResult bodyRun positive
      exact (ih (.loop body) (decClock middle) (Prod.Lex.left _ _ lower)
        supported code closed i t out r h).2
    have sim := executed_loop (refinedRemovalLocalPrice 6 bounds) body info rfl
      source target post result bodyIH reentryIH hypothesis
    exact ⟨by simpa only [compTop] using sim, sim⟩
  case rawCall dest =>
    have callee : ExecutedRawCalleeIH (refinedRemovalLocalPrice 6 bounds) dest source := by
      intro first body lookup positive i t out r h
      have eligible := global dest (.seq first body) lookup
      simp only [rawCallFramesSupported, Bool.and_eq_true] at eligible
      have lower : (decClock source).clock < source.clock := by change source.clock - 1 < source.clock; omega
      exact (ih body _ (Prod.Lex.left _ _ lower) eligible.2 global oracle i t out r h).2
    have sim := executed_raw (refinedRemovalLocalPrice 6 bounds) dest info source target post result callee hypothesis
    exact ⟨by simpa only [compTop] using sim, sim⟩
  case jumpLower r1 r2 dest =>
    have callee : ExecutedJumpIH (refinedRemovalLocalPrice 6 bounds) r1 r2 dest source := by
      intro left right program readLeft readRight compared lookup positive i t out r h
      have lower : (decClock source).clock < source.clock := by change source.clock - 1 < source.clock; omega
      exact (ih program _ (Prod.Lex.left _ _ lower) (global dest program lookup) global oracle i t out r h).1
    have sim := executed_jump (refinedRemovalLocalPrice 6 bounds) r1 r2 dest info
      source target post result callee hypothesis
    exact ⟨by simpa only [compTop] using sim, sim⟩
  case call ret dest handler =>
    cases ret with
    | none =>
      have callee : ExecutedTailCalleeIH (refinedRemovalLocalPrice 6 bounds) dest handler source := by
        intro absent program lookup positive i t out r h
        obtain ⟨key, found⟩ := execution_findCode_lookup lookup
        have lower : (decClock source).clock < source.clock := by change source.clock - 1 < source.clock; omega
        exact (ih program _ (Prod.Lex.left _ _ lower) (global key program found) global oracle i t out r h).1
      have sim := executed_tail (refinedRemovalLocalPrice 6 bounds) dest handler info
        source target post result callee hypothesis
      exact ⟨by simpa only [compTop] using sim, sim⟩
    | some packet =>
      rcases packet with ⟨ret, link, l1, l2⟩
      have entrySmall (positive : source.clock ≠ 0) :
          (decClock (setVar link (.loc l1 l2) source)).clock < source.clock := by
        change source.clock - 1 < source.clock
        omega
      have callee : ExecutedReturnCalleeIH (refinedRemovalLocalPrice 6 bounds) dest link l1 l2 source := by
        intro program lookup positive i t out r h
        obtain ⟨key, found⟩ := execution_findCode_lookup lookup
        exact (ih program _ (Prod.Lex.left _ _ (entrySmall positive))
          (global key program found) global oracle i t out r h).1
      have retSupported : rawCallFramesSupported ret = true := by
        cases handler with
        | none => simpa only [rawCallFramesSupported, Bool.and_true] using supported
        | some packet =>
          rcases packet with ⟨hp, hs, hl⟩
          simp only [rawCallFramesSupported, Bool.and_eq_true] at supported
          exact supported.1
      have returnIH : ExecutedReturnContinuationIH (refinedRemovalLocalPrice 6 bounds)
          ret dest link l1 l2 source := by
        intro program lookup positive middle bodyRun i t out r h
        obtain ⟨code, closed⟩ := RawCallFramesSupportedCode.after_evaluate program
          (decClock (setVar link (.loc l1 l2) source)) middle _ oracle global bodyRun
        have lower := Nat.lt_of_le_of_lt
          (StackSemEvaluateClock.evaluateClock _ _ _ _ bodyRun) (entrySmall positive)
        exact (ih ret middle (Prod.Lex.left _ _ lower) retSupported code closed i t out r h).2
      have exceptionIH : ExecutedExceptionContinuationIH (refinedRemovalLocalPrice 6 bounds)
          handler dest link l1 l2 source := by
        intro program hp hs hl lookup positive present middle bodyRun i t out r h
        subst handler
        have handlerSupported : rawCallFramesSupported hp = true := by
          try simp only [rawCallFramesSupported, Bool.and_eq_true] at supported
          exact supported.2
        obtain ⟨code, closed⟩ := RawCallFramesSupportedCode.after_evaluate program
          (decClock (setVar link (.loc l1 l2) source)) middle _ oracle global bodyRun
        have lower := Nat.lt_of_le_of_lt
          (StackSemEvaluateClock.evaluateClock _ _ _ _ bodyRun) (entrySmall positive)
        exact (ih hp middle (Prod.Lex.left _ _ lower) handlerSupported code closed i t out r h).2
      have sim := executed_returning bounds ret link l1 l2 dest handler info
        source target post result callee returnIH exceptionIH hypothesis
      exact ⟨by simpa only [compTop] using sim, sim⟩
termination_by (source.clock, sizeOf p)
decreasing_by exact smaller

#print axioms rawCall_cost_correct
end InitECandidate.Runtime.StackRawCall
