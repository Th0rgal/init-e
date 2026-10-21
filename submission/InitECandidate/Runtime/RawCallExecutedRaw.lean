import InitECandidate.Runtime.RawCallExecutedAtomic
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.RawCall

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open InitECandidate.Runtime.StackToLab

abbrev ExecutedRawCalleeIH {F : Type} (price : HolProg 64 → Nat) (dest : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ first body, sptLookup dest source.code = some (.seq first body) → source.clock ≠ 0 →
    ExecutedProgramIH price body (decClock source)

/-- Existing raw entries enter the actual recursively transformed body after
its prologue, with the same two-instruction local price. -/
theorem executed_raw {F : Type} (price : HolProg 64 → Nat) (dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64)) (calleeIH : ExecutedRawCalleeIH price dest source)
    (hypothesis : StackSemEvaluate.evaluate (.rawCall dest, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult price (comp info (.rawCall dest)) info target post result
      (stackExecutionCost (fun p _ => price p) (.rawCall dest) source) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change ExecutedSimulationResult price (.rawCall dest) info target post result _
  rw [StackSemEvaluate.evaluate_rawCall] at execution
  cases lookup : sptLookup dest source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
    rw [lookup] at execution
    cases program <;> simp only [destSeq] at execution
    all_goals try (exact False.elim (nonerror (Prod.mk.inj execution).1.symm))
    rename_i first body
    obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
      rawCallEntry info source target relation dest first body lookup
    have clockEq := LoopCase.stateRel_clock info source target relation
    by_cases zero : source.clock = 0
    · simp only [zero, if_true, Prod.mk.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      have targetZero : target.clock = 0 := clockEq.trans zero
      refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
        LoopCase.stateRel_emptyEnv info source target relation, ?_, by simp, ?_⟩
      · simp only [Nat.add_zero, StackSemEvaluate.evaluate_rawCall, targetLookup, destSeq,
          targetZero, if_true]
        have update : {target with clock := 0} = target := by rw [← targetZero]
        rw [update]
      · conv_lhs => rw [stackExecutionCost]
        conv_rhs => rw [stackExecutionCost]
        simp only [Nat.add_zero, targetZero, zero, if_true, Nat.le_refl]
    · simp only [zero, if_false] at execution
      rcases bodyExecution : StackSemEvaluate.evaluate (body, decClock source) with
        ⟨bodyResult, bodyPost⟩
      rw [bodyExecution] at execution
      by_cases bad : badFunReturn bodyResult = true
      · simp only [bad, if_true, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard, cost⟩ :=
          calleeIH first body lookup zero entryInfo (decClock target) bodyPost bodyResult
            ⟨bodyExecution, nonerror, LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
        have frames : stateOk info source.code := by
          obtain ⟨_, _, _, frames, _⟩ := relation
          exact frames
        have postFrames := stateOk_afterEvaluate info body (decClock source) bodyPost bodyResult frames bodyExecution
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + clock ≠ 0 := by omega
        refine ⟨clock, targetState, stackSpace,
          stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames,
          ?_, guard, ?_⟩
        · simp only [StackSemEvaluate.evaluate_rawCall, targetLookup, destSeq,
            addedNonzero, if_false,
            StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
            targetExecution, bad, Bool.false_eq_true, if_false]
        · conv_lhs => rw [stackExecutionCost]
          conv_rhs => rw [stackExecutionCost]
          simp only [addedNonzero, zero, if_false, targetLookup, lookup,
            StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero]
          exact Nat.add_le_add_left cost _

#print axioms executed_raw
end InitECandidate.Runtime.StackRawCall
