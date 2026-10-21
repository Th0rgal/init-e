import InitECandidate.Runtime.StackRemoveExecutedSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Loop
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemEvaluate Flapjack.StackSemControl Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackRemove

theorem stackExecutionCost_loop_run {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → Nat)
    (body : HolProg 64) (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F) result
    (run : evaluate (body, source) = (result, middle)) :
    stackExecutionCost price (.loop body) source = price (.loop body) source + stackExecutionCost price body source +
      (if contLoop result && middle.clock != 0 then stackExecutionCost price (.loop body) (decClock middle) else 0) := by
  rw [stackExecutionCost.eq_3, StackSemEvaluateClock.fixClockEvaluate, run]

/-- Quantitative original loop simulation; reentry is guarded by the actual
source result and remaining clock, and cost is additive across iterations. -/
theorem removalCostSimulation_loopWithPrice {F : Type} (sourcePrice targetPrice : HolProg 64 → Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (body : HolProg 64)
    (loopBound : ∀ pointer, targetPrice (.loop (comp jump bounds pointer body)) ≤ sourcePrice (.loop body))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyIH : RemovalCostSimulationFor sourcePrice targetPrice jump bounds body source)
    (reentryIH : ∀ bodyResult middle, evaluate (body, source) = (bodyResult, middle) →
      contLoop bodyResult = true → middle.clock ≠ 0 →
      RemovalCostSimulationFor sourcePrice targetPrice jump bounds (.loop body) (decClock middle)) :
    RemovalCostSimulationFor sourcePrice targetPrice jump bounds (.loop body) source := by
  intro postSource target result pointer hypothesis
  have localBound := loopBound pointer
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  rcases bodyRun : evaluate (body, source) with ⟨bodyResult, middle⟩
  have bodyNotError := StackRemove.CompCorrect.Loop.loopBodyNotError body source middle postSource bodyResult result bodyRun sourceRun notError
  obtain ⟨firstClock, middleTarget, firstTargetRun, bodyPost, firstCost⟩ :=
    bodyIH middle target bodyResult pointer
      ⟨bodyRun, bodyNotError, relation, by simpa only [StackProps.regBound] using lower⟩
  by_cases continues : StackSemControl.contLoop bodyResult = true
  · have middleRelation : stateRelHOL jump bounds pointer middle middleTarget := by
      rcases StackProps.contLoopImp bodyResult continues with same | same
      · rw [same] at bodyPost; exact bodyPost
      · rw [same] at bodyPost; exact bodyPost
    have middleClocks : middleTarget.clock = middle.clock := middleRelation.2.2.2.2.2.2.2.2.1
    by_cases zero : middle.clock = 0
    · rw [StackRemove.CompCorrect.Loop.evaluateLoopTimeOut body source middle bodyResult bodyRun continues zero] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      refine ⟨firstClock, emptyEnv middleTarget, ?_, ?_, ?_⟩
      · simpa only [comp] using
          StackRemove.CompCorrect.Loop.evaluateLoopTimeOut (comp jump bounds pointer body)
            {target with clock := firstClock + target.clock} middleTarget bodyResult
            firstTargetRun continues (middleClocks.trans zero)
      · change middleTarget.ffi = middle.ffi
        exact middleRelation.2.2.2.2.2.2.2.2.2.1
      · rw [comp, stackExecutionCost_loop_run _ _ _ _ _ firstTargetRun,
          stackExecutionCost_loop_run _ _ _ _ _ bodyRun]
        simp only [continues, middleClocks, zero, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
        change targetPrice (.loop (comp jump bounds pointer body)) + _ ≤ sourcePrice (.loop body) + _
        omega
    · rw [StackRemove.CompCorrect.Loop.evaluateLoopReentry body source middle bodyResult bodyRun continues zero] at sourceRun
      have decRelation := RelationLaws.stateRelDecClock jump bounds pointer middle middleTarget middleRelation
      obtain ⟨secondClock, postTarget, secondTargetRun, postRelation, secondCost⟩ :=
        reentryIH bodyResult middle bodyRun continues zero postSource
          (decClock middleTarget) result pointer ⟨sourceRun, notError, decRelation, lower⟩
      have notTimeout : bodyResult ≠ some .timeOut := by
        rcases StackProps.contLoopImp bodyResult continues with same | same <;> simp [same]
      have extraRun := StackProps.evaluateAddClock secondClock
        (comp jump bounds pointer body) {target with clock := firstClock + target.clock}
        bodyResult middleTarget ⟨firstTargetRun, notTimeout⟩
      have combinedRun :
          evaluate (comp jump bounds pointer body,
            {target with clock := (firstClock + secondClock) + target.clock}) =
            (bodyResult, {middleTarget with clock := secondClock + middleTarget.clock}) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
      have targetNonzero : middleTarget.clock ≠ 0 := by rw [middleClocks]; exact zero
      have boostedNonzero : ({middleTarget with clock := secondClock + middleTarget.clock}).clock ≠ 0 := by
        change secondClock + middleTarget.clock ≠ 0
        omega
      have decState : decClock {middleTarget with clock := secondClock + middleTarget.clock} =
          {decClock middleTarget with clock := secondClock + (decClock middleTarget).clock} := by
        change {middleTarget with clock := secondClock + middleTarget.clock - 1} =
          {middleTarget with clock := secondClock + (middleTarget.clock - 1)}
        have arithmetic : secondClock + middleTarget.clock - 1 = secondClock + (middleTarget.clock - 1) := by omega
        rw [arithmetic]
      refine ⟨firstClock + secondClock, postTarget, ?_, ?_, ?_⟩
      · rw [comp, StackRemove.CompCorrect.Loop.evaluateLoopReentry _ _ _ _ combinedRun continues boostedNonzero, decState]
        simpa only [comp] using secondTargetRun
      · cases result with
        | none => exact postRelation
        | some value => cases value <;> exact postRelation
      · have shiftedCost := stackExecutionCost_addClock (targetPrice)
          (comp jump bounds pointer body) {target with clock := firstClock + target.clock}
          middleTarget bodyResult firstTargetRun notTimeout secondClock
        have combinedCost : stackExecutionCost (fun p _ => targetPrice p)
            (comp jump bounds pointer body) {target with clock := (firstClock + secondClock) + target.clock} ≤
            stackExecutionCost (fun p _ => sourcePrice p) body source := by
          have eq : stackExecutionCost (fun p _ => targetPrice p)
              (comp jump bounds pointer body) {target with clock := (firstClock + secondClock) + target.clock} =
              stackExecutionCost (fun p _ => targetPrice p)
                (comp jump bounds pointer body) {target with clock := firstClock + target.clock} := by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using shiftedCost
          exact eq.le.trans firstCost
        rw [comp, stackExecutionCost_loop_run _ _ _ _ _ combinedRun,
          stackExecutionCost_loop_run _ _ _ _ _ bodyRun]
        simp only [continues, boostedNonzero, zero, bne_iff_ne, Bool.true_and, ↓reduceIte]
        simp only [if_pos boostedNonzero, if_neg zero, if_pos zero]
        rw [decState]
        change targetPrice (.loop (comp jump bounds pointer body)) + _ + _ ≤ sourcePrice (.loop body) + _ + _
        have costRest := secondCost
        simp only [comp] at costRest
        exact Nat.add_le_add (Nat.add_le_add localBound combinedCost) costRest
  · have exits : StackSemControl.contLoop bodyResult = false := by
      cases equality : StackSemControl.contLoop bodyResult <;> simp_all
    rw [StackRemove.CompCorrect.Loop.evaluateLoopExit body source middle bodyResult bodyRun exits] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨firstClock, middleTarget, ?_, ?_, ?_⟩
    · simpa only [comp] using
        StackRemove.CompCorrect.Loop.evaluateLoopExit (comp jump bounds pointer body)
          {target with clock := firstClock + target.clock} middleTarget bodyResult firstTargetRun exits
    · cases bodyResult with
      | none => simp [StackSemControl.contLoop] at continues
      | some value =>
        cases value with
        | «break» label => cases label <;> exact bodyPost
        | _ => exact bodyPost
    · rw [comp, stackExecutionCost_loop_run _ _ _ _ _ firstTargetRun,
        stackExecutionCost_loop_run _ _ _ _ _ bodyRun]
      simp only [exits, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      change targetPrice (.loop (comp jump bounds pointer body)) + _ ≤ sourcePrice (.loop body) + _
      omega

theorem removalCostSimulation_loop {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (body : HolProg 64)
    (localBound : 2 ≤ sourcePrice (.loop body))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (bodyIH : RemovalCostSimulation sourcePrice gap jump bounds body source)
    (reentryIH : ∀ bodyResult middle, evaluate (body,source) = (bodyResult,middle) →
      contLoop bodyResult = true → middle.clock ≠ 0 →
      RemovalCostSimulation sourcePrice gap jump bounds (.loop body) (decClock middle)) :
    RemovalCostSimulation sourcePrice gap jump bounds (.loop body) source :=
  removalCostSimulation_loopWithPrice sourcePrice (nativePriceWithGap gap) jump bounds body
    (fun _ => localBound) source bodyIH reentryIH

#print axioms removalCostSimulation_loopWithPrice
#print axioms removalCostSimulation_loop
end InitECandidate.Runtime.StackToLab
