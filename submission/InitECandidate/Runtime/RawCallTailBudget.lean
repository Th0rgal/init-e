import InitECandidate.Runtime.RawCallJumpBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call.Tail

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack.Compiler.Backend.StackRawCall.CallCase

theorem callee_call_allowance_le {width : Nat} [NeZero width] (p : HolProg width) (before after : Nat) :
    clockAllowance p (before - 1) after ≤ before - after - 1 := by
  have bound := clockAllowance_le p (before - 1) after
  omega

abbrev TailCalleeIH {width : Nat} [NeZero width] (C F : Type)
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) : Prop :=
  handler = none → ∀ program, findCode dest source.regs source.code = some program →
    source.clock ≠ 0 →
    ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
      (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, decClock source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info (decClock source) target →
    BoundedSimulationResult (compTop info program) info target post result
      (clockAllowance program (decClock source).clock post.clock)

theorem compCorrectCallTail {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : TailCalleeIH C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.call none dest handler)) info target post result
      (clockAllowance (.call none dest handler) source.clock post.clock) ∧
    BoundedSimulationResult (comp info (.call none dest handler)) info target post result
      (clockAllowance (.call none dest handler) source.clock post.clock) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  change BoundedSimulationResult (.call none dest handler) info target post result
      (clockAllowance (.call none dest handler) source.clock post.clock) ∧
    BoundedSimulationResult (.call none dest handler) info target post result
      (clockAllowance (.call none dest handler) source.clock post.clock)
  suffices simulation : BoundedSimulationResult (.call none dest handler) info target post result
      (clockAllowance (.call none dest handler) source.clock post.clock) by
    exact ⟨simulation, simulation⟩
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
            refine ⟨0, Nat.zero_le _, emptyEnv target, (emptyEnv target).stackSpace,
              LoopCase.stateRel_emptyEnv info source target relation, ?_, ?_⟩
            · have targetZero : target.clock = 0 := clockEq.trans zero
              simp only [Nat.add_zero, StackSemEvaluate.evaluate_call, targetLookup,
                targetZero, if_true]
              have update : {target with clock := 0} = target := by rw [← targetZero]
              rw [update]
            · simp
          · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
            rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
              ⟨bodyResult, bodyPost⟩
            rw [bodyExecution] at execution
            by_cases bad : badFunReturn bodyResult = true
            · simp only [bad, if_true, Prod.mk.injEq] at execution
              exact False.elim (nonerror execution.1.symm)
            · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
              obtain ⟨rfl, rfl⟩ := execution
              obtain ⟨clock, clockBound, targetPost, space, postRelation, targetExecution, guard⟩ :=
                calleeIH rfl program lookup zero entryInfo (decClock target) bodyPost bodyResult
                  ⟨bodyExecution, nonerror,
                    LoopCase.stateRel_decClock entryInfo source target entryRelation⟩
              have frames : stateOk info source.code := by
                obtain ⟨_, _, _, frames, _⟩ := relation
                exact frames
              have postFrames := stateOk_afterEvaluate info program (decClock source)
                bodyPost bodyResult frames bodyExecution
              refine ⟨clock, Nat.le_trans clockBound (callee_call_allowance_le program _ _), targetPost, space,
                stateRel_changeInfo entryInfo info bodyPost targetPost postRelation postFrames,
                ?_, guard⟩
              have targetNonzero : target.clock ≠ 0 := by omega
              have addedNonzero : target.clock + clock ≠ 0 := by omega
              rw [StackSemEvaluate.evaluate_call]
              simp only [targetLookup, addedNonzero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              simp only [StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
                targetExecution, bad, Bool.false_eq_true, if_false]


#print axioms compCorrectCallTail
end InitECandidate.Runtime.StackRawCall
