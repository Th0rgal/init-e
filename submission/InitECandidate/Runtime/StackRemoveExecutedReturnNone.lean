import InitECandidate.Runtime.StackExecutionCallCostEquation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallReturnNone
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone

theorem removalCostSimulation_returnNone {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (body : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (localBound : 4 + gap + callJumpWork dest ≤ sourcePrice (.call (some (body, link, l1, l2)) dest none))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (calleeIH : ∀ program, StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 → RemovalCostSimulation sourcePrice gap jump bounds program (decClock (setVar link (.loc l1 l2) source)))
    (returnIH : ∀ program middle,
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program → source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (some (.result (.loc l1 l2)), middle) →
      RemovalCostSimulation sourcePrice gap jump bounds body middle) :
    RemovalCostSimulation sourcePrice gap jump bounds (.call (some (body, link, l1, l2)) dest none) source := by
  intro postSource target result pointer hypothesis
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluateCallReturnNoneUnclamped] at sourceRun
  cases lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    obtain ⟨targetLookup, programBound⟩ := FindCode.findCodeLemmaErased jump bounds pointer
      source target dest program link ⟨relation, by
        simp only [StackProps.regBound] at bound
        cases dest <;> exact bound.1, lookup⟩
    have bodyBound : StackProps.regBound body pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.1
    have linkBound : link < pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.2.1
    by_cases zero : source.clock = 0
    · simp only [zero, if_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨0, emptyEnv target, ?_, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluateCallReturnNoneUnclamped (comp jump bounds pointer body) link l1 l2 dest target).trans (by
            simp only [targetLookup, clocks, zero, if_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
      · simpa only [comp, stackExecutionCost.eq_7, Nat.zero_add, clocks, zero, ↓reduceIte, nativePriceWithGap] using localBound
    · simp only [zero, if_false] at sourceRun
      have targetNonzero : target.clock ≠ 0 := by omega
      have entry := entryRelation jump bounds pointer link l1 l2 source target relation linkBound
      rcases bodyRun : evaluate (program, decClock (setVar link (.loc l1 l2) source)) with
        ⟨bodyResult, middle⟩
      rw [bodyRun] at sourceRun
      cases bodyResult with
      | none =>
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | error => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «break» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «continue» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | result value =>
          change (if value ≠ .loc l1 l2 then (some .error, middle)
            else evaluate (body, middle)) = (result, postSource) at sourceRun
          split at sourceRun
          · exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          · rename_i equal
            have correct : value = .loc l1 l2 := by simpa only [ne_eq, not_not] using equal
            subst value
            obtain ⟨first, middleTarget, calleeRun, middleRelation, calleeCost⟩ :=
              calleeIH program lookup zero middle
                (decClock (setVar link (.loc l1 l2) target)) (some (.result (.loc l1 l2))) pointer
                ⟨bodyRun, by simp, entry, programBound⟩
            obtain ⟨second, postTarget, returnRun, postRelation, returnCost⟩ :=
              returnIH program middle lookup zero bodyRun postSource middleTarget result pointer
                ⟨sourceRun, notError, middleRelation, bodyBound⟩
            have boosted := calleeAllowance (comp jump bounds pointer program) target middleTarget
              link l1 l2 first second targetNonzero calleeRun
            refine ⟨first + second, postTarget, ?_, ?_, ?_⟩
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              simp only [comp]
              rw [evaluateCallReturnNoneResult (comp jump bounds pointer body)
                (comp jump bounds pointer program) link l1 l2 dest
                {target with clock := (first + second) + target.clock}
                {middleTarget with clock := second + middleTarget.clock}
                targetLookup totalNonzero boosted]
              exact returnRun
            · cases result with
              | none => exact postRelation
              | some r => cases r <;> exact postRelation
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              have boostedCost : stackExecutionCost (fun p _ => nativePriceWithGap gap p)
                  (comp jump bounds pointer program)
                  (decClock (setVar link (.loc l1 l2) {target with clock := (first + second) + target.clock})) ≤
                  stackExecutionCost (fun p _ => sourcePrice p) program (decClock (setVar link (.loc l1 l2) source)) := by
                exact (stackExecutionCost_calleeAllowance (nativePriceWithGap gap)
                  (comp jump bounds pointer program) target middleTarget link l1 l2 first second _
                  targetNonzero calleeRun (by simp)).le.trans calleeCost
              rw [comp,
                stackExecutionCost_call_run (fun p _ => nativePriceWithGap gap p)
                  (comp jump bounds pointer body) (comp jump bounds pointer program) link l1 l2 dest none {target with clock := (first + second) + target.clock} _ _
                  totalNonzero targetLookup boosted,
                stackExecutionCost_call_run (fun p _ => sourcePrice p) body program link l1 l2 dest none _ _ _ zero lookup bodyRun]
              simp only [selectedContinuationBudget, ↓reduceIte]
              change _ + _ + (4 + gap + callJumpWork dest) ≤ _ + _ + sourcePrice (.call (some (body, link, l1, l2)) dest none)
              exact Nat.add_le_add (Nat.add_le_add boostedCost returnCost) localBound
        | halt _ | timeOut | finalFFI _ | exception _ =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, targetRun, postRelation, calleeCost⟩ :=
            calleeIH program lookup zero middle
              (decClock (setVar link (.loc l1 l2) target)) _ pointer
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, ?_, postRelation, ?_⟩
          · have nonzero : clock + target.clock ≠ 0 := by omega
            simp only [comp]
            rw [evaluateCallReturnNoneUnclamped]
            simp only [targetLookup, nonzero, if_false]
            rw [entryClock target link l1 l2 clock targetNonzero, targetRun]
          · have nonzero : clock + target.clock ≠ 0 := by omega
            have actualRun := targetRun
            rw [← entryClock target link l1 l2 clock targetNonzero] at actualRun
            rw [comp,
              stackExecutionCost_call_run (fun p _ => nativePriceWithGap gap p)
                (comp jump bounds pointer body) (comp jump bounds pointer program) link l1 l2 dest none {target with clock := clock + target.clock} _ _
                nonzero targetLookup actualRun,
              stackExecutionCost_call_run (fun p _ => sourcePrice p) body program link l1 l2 dest none _ _ _ zero lookup bodyRun]
            simp only [selectedContinuationBudget, Nat.add_zero]
            rw [entryClock target link l1 l2 clock targetNonzero]
            change _ + (4 + gap + callJumpWork dest) ≤ _ + sourcePrice (.call (some (body, link, l1, l2)) dest none)
            exact Nat.add_le_add calleeCost localBound


#print axioms removalCostSimulation_returnNone
end InitECandidate.Runtime.StackToLab
