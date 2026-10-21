import InitECandidate.Runtime.RawCallExecutedRaw
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.JumpLower
namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack.Compiler.Backend.StackRawCall.JumpLowerCase
open InitECandidate.Runtime.StackToLab

abbrev ExecutedJumpIH {F : Type} (price : HolProg 64 → Nat) (r1 r2 dest : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ (left right : BitVec 64) program,
    getVar r1 source = some (.word left) → getVar r2 source = some (.word right) →
    Compiler.Encoders.Asm.wordCmpHOL .lower left right = true →
    sptLookup dest source.code = some program → source.clock ≠ 0 →
    ∀ info target post result,
      StackSemEvaluate.evaluate (program, decClock source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info (decClock source) target →
      ExecutedSimulationResult price (compTop info program) info target post result
        (stackExecutionCost (fun p _ => price p) program (decClock source))

/-- A conditional lower jump charges only its actual selected callee. -/
theorem executed_jump {F : Type} (price : HolProg 64 → Nat) (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64)) (calleeIH : ExecutedJumpIH price r1 r2 dest source)
    (hypothesis : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult price (comp info (.jumpLower r1 r2 dest)) info target post result
      (stackExecutionCost (fun p _ => price p) (.jumpLower r1 r2 dest) source) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change ExecutedSimulationResult price (.jumpLower r1 r2 dest) info target post result _
  rw [StackSemEvaluate.evaluate_jumpLower] at execution
  split at execution
  · rename_i left right firstRead secondRead
    split at execution
    · rename_i lower
      simp only [findCode] at execution
      cases lookup : sptLookup dest source.code with
      | none =>
        simp only [lookup, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      | some program =>
        rw [lookup] at execution
        obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
          calleeEntry info source target relation dest program lookup
        have clockEq := LoopCase.stateRel_clock info source target relation
        by_cases zero : source.clock = 0
        · simp only [zero, if_true, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace,
            LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_, ?_⟩
          · simp only [Nat.add_zero, StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClock info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup]
            have tz : target.clock = 0 := clockEq.trans zero
            simp only [tz, if_true]
            have update : { target with clock := 0 } = target := by rw [← tz]
            rw [update]
          · simp
          · conv_lhs => rw [stackExecutionCost]
            conv_rhs => rw [stackExecutionCost]
            simp only [getVar_targetClock info source target relation, firstRead, secondRead,
              lower, if_true, zero, Nat.add_zero]
            have targetZero : target.clock = 0 := clockEq.trans zero
            simp only [targetZero, if_true, Nat.le_refl]
        · simp only [zero, if_false] at execution
          rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
            ⟨bodyResult, bodyPost⟩
          rw [bodyExecution] at execution
          by_cases bad : badFunReturn bodyResult = true
          · simp only [bad, if_true, Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
          · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            obtain ⟨clock, targetState, stackSpace, postRelation, targetExecution, guard, cost⟩ :=
              calleeIH left right program firstRead secondRead lower lookup zero
                entryInfo (decClock target) bodyPost bodyResult
                ⟨bodyExecution, nonerror,
                  LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
            have frames : stateOk info source.code := by
              obtain ⟨_, _, _, frames, _⟩ := relation
              exact frames
            have postFrames := stateOk_afterEvaluate info program (decClock source) bodyPost
              bodyResult frames bodyExecution
            have targetNonzero : target.clock ≠ 0 := by omega
            have addedNonzero : target.clock + clock ≠ 0 := by omega
            refine ⟨clock, targetState, stackSpace,
              stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames,
              ?_, guard, ?_⟩
            · simp only [StackSemEvaluate.evaluate_jumpLower,
                getVar_targetClock info source target relation, firstRead, secondRead,
                lower, if_true, findCode, targetLookup, addedNonzero, if_false,
                StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
                targetExecution, bad, Bool.false_eq_true, if_false]
            · conv_lhs => rw [stackExecutionCost]
              conv_rhs => rw [stackExecutionCost]
              simp only [getVar_targetClock info source target relation, firstRead, secondRead,
                lower, if_true, addedNonzero, zero, if_false, findCode, targetLookup, lookup,
                StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero]
              exact Nat.add_le_add_left cost _
    · rename_i notLower
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      refine ⟨0, target, target.stackSpace, relation, ?_, (fun _ => rfl), ?_⟩
      · simp only [StackSemEvaluate.evaluate_jumpLower,
          getVar_targetClock info source target relation, firstRead, secondRead,
          notLower, Bool.false_eq_true, if_false]
        have update : { target with clock := target.clock + 0 } = target := by
          cases target
          simp
        rw [update]
      · conv_lhs => rw [stackExecutionCost]
        conv_rhs => rw [stackExecutionCost]
        simp only [getVar_targetClock info source target relation, firstRead, secondRead,
          notLower, Bool.false_eq_true, if_false, Nat.le_refl]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)

#print axioms executed_jump
end InitECandidate.Runtime.StackRawCall
