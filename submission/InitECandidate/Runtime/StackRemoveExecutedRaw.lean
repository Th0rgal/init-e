import InitECandidate.Runtime.StackRemoveExecutedSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.RawCall
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackRemove

theorem removalCostSimulation_raw {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (label : Nat) (localBound : 2 ≤ sourcePrice (.rawCall label))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (calleeIH : ∀ frame body, sptLookup label source.code = some (.seq frame body) →
      source.clock ≠ 0 → RemovalCostSimulation sourcePrice gap jump body (decClock source)) :
    RemovalCostSimulation sourcePrice gap jump (.rawCall label) source := by
  intro postSource target result pointer bounds hypothesis
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_rawCall] at sourceRun
  cases lookup : sptLookup label source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    cases shape : StackSemControl.destSeq program with
    | none =>
      simp only [shape] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | some pair =>
      rcases pair with ⟨frame, body⟩
      have programEq : program = .seq frame body := by
        cases program <;> simp [StackSemControl.destSeq] at shape ⊢
        exact ⟨shape.1, shape.2⟩
      subst program
      simp only [StackSemControl.destSeq] at sourceRun
      obtain ⟨targetLookup, programBound⟩ := FindCode.findCodeLemma jump bounds pointer
        source target (.inl label) (.seq frame body) ⟨relation, True.intro, lookup⟩
      change sptLookup label target.code = some (comp jump bounds pointer (.seq frame body)) at targetLookup
      simp only [comp] at targetLookup
      change StackProps.regBound frame pointer ∧ StackProps.regBound body pointer at programBound
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, emptyEnv target, ?_, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_rawCall label target).trans (by
              simp only [targetLookup, StackSemControl.destSeq, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
        · simp only [comp]
          rw [stackExecutionCost.eq_5, stackExecutionCost.eq_5]
          simpa only [Nat.zero_add, clocks, zero, ↓reduceIte, nativePriceWithGap] using localBound
      · simp only [zero, if_false] at sourceRun
        rcases bodyRun : evaluate (body, decClock source) with ⟨bodyResult, middle⟩
        rw [bodyRun] at sourceRun
        by_cases bad : StackSemControl.badFunReturn bodyResult = true
        · simp only [bad, if_true] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        · simp [bad] at sourceRun
          rcases sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation, calleeCost⟩ :=
            calleeIH frame body lookup zero middle (decClock target) bodyResult pointer bounds
              ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, programBound.2⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          have clockEq : decClock {target with clock := clock + target.clock} =
              {decClock target with clock := clock + (decClock target).clock} := by
            simp only [decClock]
            congr 1
            omega
          refine ⟨clock, postTarget, ?_, ?_, ?_⟩
          · simp only [comp]
            rw [evaluate_rawCall]
            simp only [targetLookup, StackSemControl.destSeq, nonzero, if_false]
            rw [clockEq, targetRun]
            simp [bad]
          · cases bodyResult with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
          · simp only [comp]
            rw [stackExecutionCost.eq_5, stackExecutionCost.eq_5]
            simp only [nonzero, zero, ↓reduceIte, targetLookup, lookup]
            rw [clockEq]
            change 2 + _ ≤ sourcePrice (.rawCall label) + _
            exact Nat.add_le_add localBound calleeCost

#print axioms removalCostSimulation_raw
end InitECandidate.Runtime.StackToLab
