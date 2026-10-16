import InitECandidate.Runtime.RawCallIfBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.JumpLower

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack.Compiler.Backend.StackRawCall.JumpLowerCase

theorem callee_allowance_le {width : Nat} [NeZero width] (p : HolProg width) (before after : Nat) :
    clockAllowance p (before - 1) after ≤ before - after :=
  Nat.le_trans (clockAllowance_le p _ _) (Nat.sub_le_sub_right (Nat.sub_le before 1) after)

abbrev TopProgramIH {width : Nat} [NeZero width] (C F : Type) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target →
    BoundedSimulationResult (compTop info program) info target post result
      (clockAllowance program source.clock post.clock)

/-- Actual selected-callee evaluate_ind hypothesis at the fixed decClock
source. Operand reads, the unsigned comparison, code lookup and nonzero clock
are precisely the guards of the original recursive call. -/
abbrev JumpIH {width : Nat} [NeZero width] (C F : Type) (r1 r2 dest : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (left right : BitVec width) (program : HolProg width),
    StackSemStateOps.getVar r1 source = some (.word left) →
    StackSemStateOps.getVar r2 source = some (.word right) →
    Compiler.Encoders.Asm.wordCmpHOL .lower left right = true →
    sptLookup dest source.code = some program →
    source.clock ≠ 0 → TopProgramIH C F program (decClock source)

abbrev CalleeIH {width : Nat} [NeZero width] (C F : Type) (dest : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ first body, sptLookup dest source.code = some (.seq first body) →
    source.clock ≠ 0 → ProgramIH C F body (decClock source)

theorem compCorrectJumpLower {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : JumpIH C F r1 r2 dest source)
    (hypothesis : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.jumpLower r1 r2 dest)) info target post result (source.clock - post.clock) ∧
    BoundedSimulationResult (comp info (.jumpLower r1 r2 dest)) info target post result (source.clock - post.clock) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change BoundedSimulationResult (.jumpLower r1 r2 dest) info target post result (source.clock - post.clock) ∧
    BoundedSimulationResult (.jumpLower r1 r2 dest) info target post result (source.clock - post.clock)
  suffices simulation : BoundedSimulationResult (.jumpLower r1 r2 dest) info target post result (source.clock - post.clock) by
    exact ⟨simulation, simulation⟩
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
          refine ⟨0, Nat.zero_le _, emptyEnv target, (emptyEnv target).stackSpace,
            LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
          · simp only [Nat.add_zero, StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClock info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup]
            have tz : target.clock = 0 := clockEq.trans zero
            simp only [tz, if_true]
            have update : { target with clock := 0 } = target := by rw [← tz]
            rw [update]
          · simp
        · simp only [zero, if_false] at execution
          rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
            ⟨bodyResult, bodyPost⟩
          rw [bodyExecution] at execution
          by_cases bad : badFunReturn bodyResult = true
          · simp only [bad, if_true, Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
          · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            obtain ⟨clock, clockBound, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
              calleeIH left right program firstRead secondRead lower lookup zero
                entryInfo (decClock target) bodyPost bodyResult
                ⟨bodyExecution, nonerror,
                  LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
            have frames : stateOk info source.code := by
              obtain ⟨_, _, _, frames, _⟩ := relation
              exact frames
            have postFrames := stateOk_afterEvaluate info program (decClock source) bodyPost
              bodyResult frames bodyExecution
            refine ⟨clock, Nat.le_trans clockBound (callee_allowance_le program _ _), targetState, stackSpace,
              stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames,
              ?_, guard⟩
            have targetNonzero : target.clock ≠ 0 := by omega
            have addedNonzero : target.clock + clock ≠ 0 := by omega
            simp only [StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClock info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup, addedNonzero, if_false,
              StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
              targetExecution, bad, Bool.false_eq_true, if_false]
    · rename_i notLower
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      refine ⟨0, Nat.zero_le _, target, target.stackSpace, relation, ?_, fun _ => rfl⟩
      simp only [StackSemEvaluate.evaluate_jumpLower,
        getVar_targetClock info source target relation, firstRead, secondRead,
        notLower, Bool.false_eq_true, if_false]
      have update : { target with clock := target.clock + 0 } = target := by
        cases target
        simp
      rw [update]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)


theorem compCorrectRawCall {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : CalleeIH C F dest source)
    (hypothesis : StackSemEvaluate.evaluate (.rawCall dest, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.rawCall dest)) info target resultState result (source.clock - resultState.clock) ∧
    BoundedSimulationResult (comp info (.rawCall dest)) info target resultState result (source.clock - resultState.clock) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change BoundedSimulationResult (.rawCall dest) info target resultState result (source.clock - resultState.clock) ∧
    BoundedSimulationResult (.rawCall dest) info target resultState result (source.clock - resultState.clock)
  suffices simulation : BoundedSimulationResult (.rawCall dest) info target resultState result (source.clock - resultState.clock) by
    exact ⟨simulation, simulation⟩
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
      refine ⟨0, Nat.zero_le _, emptyEnv target, (emptyEnv target).stackSpace,
        LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
      · simp only [Nat.add_zero, StackSemEvaluate.evaluate_rawCall, targetLookup,
          destSeq]
        have tz : target.clock = 0 := clockEq.trans zero
        simp only [tz, if_true]
        have update : { target with clock := 0 } = target := by
          rw [← tz]
        rw [update]
      · simp
    · simp only [zero, if_false] at execution
      rcases bodyExecution : StackSemEvaluate.evaluate (body, decClock source) with
        ⟨bodyResult, bodyPost⟩
      rw [bodyExecution] at execution
      by_cases bad : badFunReturn bodyResult = true
      · simp only [bad, if_true, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨clock, clockBound, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
          calleeIH first body lookup zero entryInfo (decClock target) bodyPost bodyResult
            ⟨bodyExecution, nonerror,
              LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
        have frames : stateOk info source.code := by
          obtain ⟨_, _, _, frames, _⟩ := relation
          exact frames
        have postFrames := stateOk_afterEvaluate info body (decClock source) bodyPost
          bodyResult frames bodyExecution
        refine ⟨clock, Nat.le_trans clockBound (callee_allowance_le body _ _), targetState, stackSpace,
          stateRel_changeInfo entryInfo info bodyPost targetState postRelation postFrames,
          ?_, guard⟩
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + clock ≠ 0 := by omega
        simp only [StackSemEvaluate.evaluate_rawCall, targetLookup, destSeq,
          addedNonzero, if_false,
          StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
          targetExecution, bad, Bool.false_eq_true, if_false]


#print axioms compCorrectRawCall
#print axioms compCorrectJumpLower
end InitECandidate.Runtime.StackRawCall
