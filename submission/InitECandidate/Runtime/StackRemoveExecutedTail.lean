import InitECandidate.Runtime.StackRemoveExecutedSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallTail
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackRemove

theorem removalCostSimulation_tail {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (dest : Sum Nat Nat) (handler : Option (HolProg 64 × Nat × Nat))
    (localBound : callJumpWork dest ≤ sourcePrice (.call none dest handler))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (calleeIH : ∀ program, StackSemControl.findCode dest source.regs source.code = some program →
      handler = none → source.clock ≠ 0 →
      RemovalCostSimulation sourcePrice gap jump program (decClock source)) :
    RemovalCostSimulation sourcePrice gap jump (.call none dest handler) source := by
  intro postSource target result pointer bounds hypothesis
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_call] at sourceRun
  cases lookup : StackSemControl.findCode dest source.regs source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    cases handler with
    | some h =>
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | none =>
      obtain ⟨targetLookup, bodyBound⟩ := FindCode.findCodeLemma jump bounds pointer
        source target dest program ⟨relation, by
          simp only [StackProps.regBound] at bound
          cases dest <;> exact bound.1, lookup⟩
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, emptyEnv target, ?_, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_call none dest none target).trans (by
              simp only [targetLookup, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
        · rw [comp, stackExecutionCost.eq_6, stackExecutionCost.eq_6]
          simpa only [Nat.zero_add, clocks, zero, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, nativePriceWithGap] using localBound
      · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at sourceRun
        rcases bodyRun : evaluate (program, decClock source) with ⟨bodyResult, middle⟩
        rw [bodyRun] at sourceRun
        by_cases bad : StackSemControl.badFunReturn bodyResult = true
        · simp only [bad, if_true] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        · simp [bad] at sourceRun
          rcases sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation, calleeCost⟩ :=
            calleeIH program lookup rfl zero middle (decClock target) bodyResult pointer bounds
              ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, bodyBound⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          have clockEq : decClock {target with clock := clock + target.clock} =
              {decClock target with clock := clock + (decClock target).clock} := by
            simp only [decClock]
            congr 1
            omega
          refine ⟨clock, postTarget, ?_, ?_, ?_⟩
          · simp only [comp]
            rw [evaluate_call]
            simp only [targetLookup, nonzero, if_false, StackSemEvaluateClock.fixClockEvaluate]
            rw [clockEq, targetRun]
            simp [bad]
          · cases bodyResult with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
          · rw [comp, stackExecutionCost.eq_6, stackExecutionCost.eq_6]
            simp only [Option.isSome_none, Bool.false_eq_true, nonzero, zero, ↓reduceIte,
              targetLookup, lookup]
            rw [clockEq]
            change callJumpWork dest + _ ≤ sourcePrice (.call none dest none) + _
            exact Nat.add_le_add localBound calleeCost

#print axioms removalCostSimulation_tail
end InitECandidate.Runtime.StackToLab
