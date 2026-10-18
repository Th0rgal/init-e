import InitECandidate.Runtime.StackRemoveWork
import InitECandidate.Runtime.StackRemovePathWork
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.If

namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.Seq
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.If
theorem compCorrectSeq_path_bounded {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (firstIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
      (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ Flapjack.Compiler.Backend.StackProps.regBound first k →
      ∃ clock, clock ≤ removePathWork first source ∧ ∃ postTarget,
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (secondIH : ∀ (middle : StackSemStateFiniteExact width C F),
      evaluate (first, source) = (none, middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k middle t ∧ Flapjack.Compiler.Backend.StackProps.regBound second k →
      ∃ clock, clock ≤ removePathWork second middle ∧ ∃ postTarget,
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.seq first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.seq first second) pointer) :
    ∃ clock, clock ≤ removePathWork (.seq first second) source ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.seq first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change Flapjack.Compiler.Backend.StackProps.regBound first pointer ∧ Flapjack.Compiler.Backend.StackProps.regBound second pointer at lower
  rcases firstRun : evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
    have workEq : removePathWork (.seq first second) source =
        2 + removePathWork first source + removePathWork second middle := by
      rw [removePathWork, StackSemEvaluateClock.fixClockEvaluate, firstRun]
    rw [evaluateSeqNone first second source middle firstRun] at sourceRun
    obtain ⟨firstClock, firstBound, middleTarget, firstTargetRun, middleRelation⟩ :=
      firstIH none middle target pointer bounds jump ⟨firstRun, by simp, relation, lower.1⟩
    change stateRelHOL jump bounds pointer middle middleTarget at middleRelation
    obtain ⟨secondClock, secondBound, postTarget, secondTargetRun, postRelation⟩ :=
      secondIH middle firstRun result postSource middleTarget pointer bounds jump
        ⟨sourceRun, notError, middleRelation, lower.2⟩
    have extraRun := Flapjack.Compiler.Backend.StackProps.evaluateAddClock secondClock
      (comp jump bounds pointer first) {target with clock := firstClock + target.clock}
      none middleTarget ⟨firstTargetRun, by simp⟩
    have combinedRun :
        evaluate (comp jump bounds pointer first,
          {target with clock := (firstClock + secondClock) + target.clock}) =
          (none, {middleTarget with clock := secondClock + middleTarget.clock}) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
    refine ⟨firstClock + secondClock, by rw [workEq]; omega, postTarget, ?_, ?_⟩
    · rw [comp, evaluateSeqNone _ _ _ _ combinedRun]
      exact secondTargetRun
    · cases result with
      | none => exact postRelation
      | some value => cases value <;> exact postRelation
  | some firstResult =>
    have workEq : removePathWork (.seq first second) source =
        2 + removePathWork first source + 0 := by
      rw [removePathWork, StackSemEvaluateClock.fixClockEvaluate, firstRun]
    rw [evaluateSeqSome first second source middle firstResult firstRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨clock, bound, postTarget, targetRun, postRelation⟩ :=
      firstIH (some firstResult) middle target pointer bounds jump
        ⟨firstRun, notError, relation, lower.1⟩
    refine ⟨clock, by rw [workEq]; omega, postTarget, ?_, ?_⟩
    · rw [comp, evaluateSeqSome _ _ _ _ _ targetRun]
    · cases firstResult <;> exact postRelation
theorem compCorrectIf_path_bounded {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (firstIH : ∀ (left right : WordLocW width),
      getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some true →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ Flapjack.Compiler.Backend.StackProps.regBound first k →
      ∃ clock, clock ≤ removePathWork first source ∧ ∃ postTarget,
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (secondIH : ∀ (left right : WordLocW width),
      getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some false →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ Flapjack.Compiler.Backend.StackProps.regBound second k →
      ∃ clock, clock ≤ removePathWork second source ∧ ∃ postTarget,
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.ite comparison register operand first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.ite comparison register operand first second) pointer) :
    ∃ clock, clock ≤ removePathWork (.ite comparison register operand first second) source ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.ite comparison register operand first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  simp only [Flapjack.Compiler.Backend.StackProps.regBound] at lower
  have leftEq := RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower.1⟩
  have rightEq := operandLookup jump bounds pointer source target operand relation lower.2.1
  rw [evaluate_ite] at sourceRun
  cases leftLookup : getVar register source with
  | none =>
    rw [leftLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some left =>
    rw [leftLookup] at sourceRun
    cases rightLookup : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source with
    | none =>
      rw [rightLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some right =>
      rw [rightLookup] at sourceRun
      simp only [] at sourceRun
      cases compared : wordSemWordCmp comparison left right with
      | none =>
        rw [compared] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some truth =>
        cases truth with
        | false =>
          rw [compared] at sourceRun
          obtain ⟨clock, bound, postTarget, targetRun, postRelation⟩ :=
            secondIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.2⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, by rw [removePathWork]; simp only [StackToLab.selectedBranchBudget, leftLookup, rightLookup, compared]; omega, postTarget, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
        | true =>
          rw [compared] at sourceRun
          obtain ⟨clock, bound, postTarget, targetRun, postRelation⟩ :=
            firstIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.1⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, by rw [removePathWork]; simp only [StackToLab.selectedBranchBudget, leftLookup, rightLookup, compared]; omega, postTarget, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
#print axioms compCorrectSeq_path_bounded
#print axioms compCorrectIf_path_bounded
end InitECandidate.Runtime.StackRemove
