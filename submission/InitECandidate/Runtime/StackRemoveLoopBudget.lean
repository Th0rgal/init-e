import InitECandidate.Runtime.StackRemoveWork
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Loop

namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop
theorem compCorrectLoop_bounded {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (bodyIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
      (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ Flapjack.Compiler.Backend.StackProps.regBound body k →
      ∃ clock, clock ≤ removeWork body source ∧ ∃ postTarget,
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (reentryIH : ∀ (bodyResult : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      evaluate (body, source) = (bodyResult, middle) →
      StackSemControl.contLoop bodyResult = true → middle.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (.loop body, decClock middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock middle) t ∧ Flapjack.Compiler.Backend.StackProps.regBound (.loop body) k →
      ∃ clock, clock ≤ removeWork (.loop body) (decClock middle) ∧ ∃ postTarget,
        evaluate (comp j off k (.loop body), {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.loop body, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.loop body) pointer) :
    ∃ clock, clock ≤ removeWork (.loop body) source ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.loop body),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  rcases bodyRun : evaluate (body, source) with ⟨bodyResult, middle⟩
  have workEq : removeWork (.loop body) source = 2 + removeWork body source +
      (if contLoop bodyResult && middle.clock != 0 then removeWork (.loop body) (decClock middle) else 0) := by
    rw [removeWork, StackSemEvaluateClock.fixClockEvaluate, bodyRun]
  have bodyNotError := loopBodyNotError body source middle postSource bodyResult result bodyRun sourceRun notError
  obtain ⟨firstClock, firstBound, middleTarget, firstTargetRun, bodyPost⟩ :=
    bodyIH bodyResult middle target pointer bounds jump
      ⟨bodyRun, bodyNotError, relation, by simpa only [Flapjack.Compiler.Backend.StackProps.regBound] using lower⟩
  by_cases continues : StackSemControl.contLoop bodyResult = true
  · have middleRelation : stateRelHOL jump bounds pointer middle middleTarget := by
      rcases Flapjack.Compiler.Backend.StackProps.contLoopImp bodyResult continues with same | same
      · rw [same] at bodyPost; exact bodyPost
      · rw [same] at bodyPost; exact bodyPost
    have middleClocks : middleTarget.clock = middle.clock := middleRelation.2.2.2.2.2.2.2.2.1
    by_cases zero : middle.clock = 0
    · rw [evaluateLoopTimeOut body source middle bodyResult bodyRun continues zero] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      refine ⟨firstClock, by rw [workEq]; omega, emptyEnv middleTarget, ?_, ?_⟩
      · simpa only [comp] using
          evaluateLoopTimeOut (comp jump bounds pointer body)
            {target with clock := firstClock + target.clock} middleTarget bodyResult
            firstTargetRun continues (middleClocks.trans zero)
      · change middleTarget.ffi = middle.ffi
        exact middleRelation.2.2.2.2.2.2.2.2.2.1
    · rw [evaluateLoopReentry body source middle bodyResult bodyRun continues zero] at sourceRun
      have decRelation := RelationLaws.stateRelDecClock jump bounds pointer middle middleTarget middleRelation
      obtain ⟨secondClock, secondBound, postTarget, secondTargetRun, postRelation⟩ :=
        reentryIH bodyResult middle bodyRun continues zero result postSource
          (decClock middleTarget) pointer bounds jump ⟨sourceRun, notError, decRelation, lower⟩
      have notTimeout : bodyResult ≠ some .timeOut := by
        rcases Flapjack.Compiler.Backend.StackProps.contLoopImp bodyResult continues with same | same <;> simp [same]
      have extraRun := Flapjack.Compiler.Backend.StackProps.evaluateAddClock secondClock
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
      refine ⟨firstClock + secondClock, by
        have budgetEq : removeWork (.loop body) source =
            2 + removeWork body source + removeWork (.loop body) (decClock middle) := by
          simp [workEq, continues, zero]
        rw [budgetEq]
        omega, postTarget, ?_, ?_⟩
      · rw [comp, evaluateLoopReentry _ _ _ _ combinedRun continues boostedNonzero, decState]
        simpa only [comp] using secondTargetRun
      · cases result with
        | none => exact postRelation
        | some value => cases value <;> exact postRelation
  · have exits : StackSemControl.contLoop bodyResult = false := by
      cases equality : StackSemControl.contLoop bodyResult <;> simp_all
    rw [evaluateLoopExit body source middle bodyResult bodyRun exits] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨firstClock, by rw [workEq]; omega, middleTarget, ?_, ?_⟩
    · simpa only [comp] using
        evaluateLoopExit (comp jump bounds pointer body)
          {target with clock := firstClock + target.clock} middleTarget bodyResult firstTargetRun exits
    · cases bodyResult with
      | none => simp [StackSemControl.contLoop] at continues
      | some value =>
        cases value with
        | «break» label => cases label <;> exact bodyPost
        | _ => exact bodyPost
#print axioms compCorrectLoop_bounded
end InitECandidate.Runtime.StackRemove
