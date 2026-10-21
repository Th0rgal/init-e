import InitECandidate.Runtime.RawCallExecutedOptimized
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Tail

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.CallCase
open InitECandidate.Runtime.StackToLab

/-- Callee IH uses the actual top-level compiler and the entry info selected
by the original raw-call state relation, rather than assuming unchanged code. -/
abbrev ExecutedTailCalleeIH {F : Type} (price : HolProg 64 → Nat)
    (dest : Sum Nat Nat) (handler : Option (HolProg 64 × Nat × Nat))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  handler = none → ∀ program, findCode dest source.regs source.code = some program →
    source.clock ≠ 0 →
    ∀ info target post result,
      StackSemEvaluate.evaluate (program, decClock source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info (decClock source) target →
      ExecutedSimulationResult price (compTop info program) info target post result
        (stackExecutionCost (fun p _ => price p) program (decClock source))

/-- Actual tail-call simulation with cost transfer through the selected,
recursively compiled callee, including timeouts and resource exits. -/
theorem executed_tail {F : Type} (price : HolProg 64 → Nat)
    (dest : Sum Nat Nat) (handler : Option (HolProg 64 × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (calleeIH : ExecutedTailCalleeIH price dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult price (comp info (.call none dest handler)) info target post result
      (stackExecutionCost (fun p _ => price p) (.call none dest handler) source) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change ExecutedSimulationResult price (.call none dest handler) info target post result _
  rw [StackSemEvaluate.evaluate_call] at execution
  cases lookup : findCode dest source.regs source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
    rw [lookup] at execution
    cases handler with
    | some handler =>
      simp only [Prod.mk.injEq] at execution
      exact False.elim (nonerror execution.1.symm)
    | none =>
      obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
        callEntry info source target relation dest program lookup
      have clockEq := LoopCase.stateRel_clock info source target relation
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        have targetZero : target.clock = 0 := clockEq.trans zero
        refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
          LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_, ?_⟩
        · simp only [Nat.add_zero, StackSemEvaluate.evaluate_call, targetLookup, targetZero, if_true]
          have update : {target with clock := 0} = target := by rw [← targetZero]
          rw [update]
        · simp
        · conv_lhs => rw [stackExecutionCost]
          conv_rhs => rw [stackExecutionCost]
          simp only [Option.isSome_none, Bool.false_eq_true, if_false, Nat.add_zero,
            targetZero, zero, if_true, Nat.le_refl]
      · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
        rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
          ⟨bodyResult, bodyPost⟩
        rw [bodyExecution] at execution
        by_cases bad : badFunReturn bodyResult = true
        · simp only [bad, if_true, Prod.mk.injEq] at execution
          exact False.elim (nonerror execution.1.symm)
        · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          obtain ⟨clock, targetPost, space, postRelation, targetExecution, guard, cost⟩ :=
            calleeIH rfl program lookup zero entryInfo (decClock target) bodyPost bodyResult
              ⟨bodyExecution, nonerror, LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
          have frames : stateOk info source.code := by
            obtain ⟨_, _, _, frames, _⟩ := relation
            exact frames
          have postFrames := RawCallCase.stateOk_afterEvaluate info program (decClock source)
            bodyPost bodyResult frames bodyExecution
          have targetNonzero : target.clock ≠ 0 := by omega
          have addedNonzero : target.clock + clock ≠ 0 := by omega
          refine ⟨clock, targetPost, space,
            RawCallCase.stateRel_changeInfo entryInfo info bodyPost targetPost postRelation postFrames,
            ?_, guard, ?_⟩
          · rw [StackSemEvaluate.evaluate_call]
            simp only [targetLookup, addedNonzero, if_false]
            rw [StackSemEvaluateClock.fixClockEvaluate]
            simp only [StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
              targetExecution, bad, Bool.false_eq_true, if_false]
          · conv_lhs => rw [stackExecutionCost]
            conv_rhs => rw [stackExecutionCost]
            simp only [Option.isSome_none, Bool.false_eq_true, if_false, addedNonzero, zero,
              targetLookup, lookup,
              StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero]
            exact Nat.add_le_add_left cost _

#print axioms executed_tail
end InitECandidate.Runtime.StackRawCall
