import InitECandidate.Runtime.StackRemoveWork
import InitECandidate.Runtime.StackRemovePathWork
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CallTail
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.JumpLower
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.RawCall

namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.Compiler.Encoders.Asm
theorem compCorrectCallTail_path_bounded {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (program : HolProg width),
      StackSemControl.findCode dest source.regs source.code = some program →
      handler = none → source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ Flapjack.Compiler.Backend.StackProps.regBound program k →
      ∃ clock, clock ≤ removePathWork program (decClock source) ∧ ∃ postTarget,
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.call none dest handler, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.call none dest handler : HolProg width) pointer) :
    ∃ clock, clock ≤ removePathWork (.call none dest handler) source ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.call none dest handler),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
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
          simp only [Flapjack.Compiler.Backend.StackProps.regBound] at bound
          cases dest <;> exact bound.1, lookup⟩
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, Nat.zero_le _, emptyEnv target, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_call none dest none target).trans (by
              simp only [targetLookup, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
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
          obtain ⟨clock, allowanceBound, postTarget, targetRun, postRelation⟩ :=
            calleeIH program lookup rfl zero bodyResult middle (decClock target) pointer bounds jump
              ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, bodyBound⟩
          refine ⟨clock, by
            simp only [removePathWork, if_neg zero, lookup]
            omega, postTarget, ?_, ?_⟩
          swap
          · cases bodyResult with
            | none => exact postRelation
            | some r => cases r <;> exact postRelation
          have nonzero : clock + target.clock ≠ 0 := by omega
          have clockEq : decClock {target with clock := clock + target.clock} =
              {decClock target with clock := clock + (decClock target).clock} := by
            simp only [decClock]
            congr 1
            omega
          simp only [comp]
          rw [evaluate_call]
          simp only [targetLookup, nonzero, if_false, StackSemEvaluateClock.fixClockEvaluate]
          rw [clockEq, targetRun]
          simp [bad]
theorem compCorrectJumpLower_path_bounded {width : Nat} [NeZero width] {C F : Type}
    (first second label : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (left right : BitVec width) (program : HolProg width),
      getVar first source = some (.word left) → getVar second source = some (.word right) →
      wordCmpHOL .lower left right = true → sptLookup label source.code = some program →
      source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ Flapjack.Compiler.Backend.StackProps.regBound program k →
      ∃ clock, clock ≤ removePathWork program (decClock source) ∧ ∃ postTarget,
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.jumpLower first second label, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.jumpLower first second label : HolProg width) pointer) :
    ∃ clock, clock ≤ removePathWork (.jumpLower first second label) source ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.jumpLower first second label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer at bound
  have readFirst := RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩
  have readSecond := RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2⟩
  change source.regs.lookup first = target.regs.lookup first at readFirst
  change source.regs.lookup second = target.regs.lookup second at readSecond
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_jumpLower] at sourceRun
  cases hFirst : getVar first source with
  | none =>
    simp only [hFirst] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some left =>
    cases left with
    | loc name offset =>
      simp only [hFirst] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word left =>
      cases hSecond : getVar second source with
      | none =>
        simp only [hFirst, hSecond] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some right =>
        cases right with
        | loc name offset =>
          simp only [hFirst, hSecond] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word right =>
          simp only [hFirst, hSecond] at sourceRun
          have targetFirst : target.regs.lookup first = some (.word left) := readFirst.symm.trans hFirst
          have targetSecond : target.regs.lookup second = some (.word right) := readSecond.symm.trans hSecond
          by_cases lower : wordCmpHOL .lower left right = true
          · simp only [lower, if_true, StackSemControl.findCode] at sourceRun
            cases lookup : sptLookup label source.code with
            | none =>
              simp only [lookup] at sourceRun
              exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
            | some program =>
              simp only [lookup] at sourceRun
              obtain ⟨targetLookup, bodyBound⟩ := FindCode.codeLookup jump bounds pointer label source target program relation lookup
              by_cases zero : source.clock = 0
              · simp only [zero, if_true] at sourceRun
                rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
                subst result
                subst postSource
                refine ⟨0, Nat.zero_le _, emptyEnv target, ?_, ?_⟩
                · simpa only [comp, Nat.zero_add] using
                    (evaluate_jumpLower first second label target).trans (by
                      simp only [getVar, targetFirst, targetSecond, lower, if_true,
                        StackSemControl.findCode, targetLookup, clocks, zero])
                · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
              · simp only [zero, if_false] at sourceRun
                rcases bodyRun : evaluate (program, decClock source) with ⟨bodyResult, middle⟩
                rw [bodyRun] at sourceRun
                by_cases bad : StackSemControl.badFunReturn bodyResult = true
                · simp only [bad, if_true] at sourceRun
                  exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                · simp [bad] at sourceRun
                  rcases sourceRun with ⟨resultEq, postEq⟩
                  subst result
                  subst postSource
                  obtain ⟨clock, allowanceBound, postTarget, targetRun, postRelation⟩ :=
                    calleeIH left right program hFirst hSecond lower lookup zero bodyResult middle
                      (decClock target) pointer bounds jump
                      ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, bodyBound⟩
                  refine ⟨clock, by
                    rw [removePathWork]
                    simp only [hFirst, hSecond, lower, if_true, if_neg zero, StackSemControl.findCode, lookup]
                    omega, postTarget, ?_, ?_⟩
                  swap
                  · cases bodyResult with
                    | none => exact postRelation
                    | some r => cases r <;> exact postRelation
                  have nonzero : clock + target.clock ≠ 0 := by omega
                  have clockEq : decClock {target with clock := clock + target.clock} =
                      {decClock target with clock := clock + (decClock target).clock} := by
                    simp only [decClock]
                    congr 1
                    omega
                  simp only [comp]
                  rw [evaluate_jumpLower]
                  simp only [getVar, targetFirst, targetSecond, StackSemControl.findCode,
                    targetLookup, lower, if_true, nonzero, if_false]
                  rw [clockEq, targetRun]
                  simp [bad]
          · simp [lower] at sourceRun
            rcases sourceRun with ⟨resultEq, postEq⟩
            subst result
            subst postSource
            refine ⟨0, Nat.zero_le _, target, ?_, relation⟩
            simpa only [comp, Nat.zero_add] using
              (evaluate_jumpLower first second label target).trans (by
                simp [getVar, targetFirst, targetSecond, lower])
theorem compCorrectRawCall_path_bounded {width : Nat} [NeZero width] {C F : Type}
    (label : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (frame body : HolProg width),
      sptLookup label source.code = some (.seq frame body) → source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ Flapjack.Compiler.Backend.StackProps.regBound body k →
      ∃ clock, clock ≤ removePathWork body (decClock source) ∧ ∃ postTarget,
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.rawCall label, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.rawCall label : HolProg width) pointer) :
    ∃ clock, clock ≤ removePathWork (.rawCall label) source ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.rawCall label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
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
      change Flapjack.Compiler.Backend.StackProps.regBound frame pointer ∧ Flapjack.Compiler.Backend.StackProps.regBound body pointer at programBound
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, Nat.zero_le _, emptyEnv target, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_rawCall label target).trans (by
              simp only [targetLookup, StackSemControl.destSeq, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
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
          obtain ⟨clock, allowanceBound, postTarget, targetRun, postRelation⟩ :=
            calleeIH frame body lookup zero bodyResult middle (decClock target) pointer bounds jump
              ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, programBound.2⟩
          refine ⟨clock, by
            simp only [removePathWork, if_neg zero, StackSemControl.findCode, lookup]
            omega, postTarget, ?_, ?_⟩
          swap
          · cases bodyResult with
            | none => exact postRelation
            | some r => cases r <;> exact postRelation
          have nonzero : clock + target.clock ≠ 0 := by omega
          have clockEq : decClock {target with clock := clock + target.clock} =
              {decClock target with clock := clock + (decClock target).clock} := by
            simp only [decClock]
            congr 1
            omega
          simp only [comp]
          rw [evaluate_rawCall]
          simp only [targetLookup, StackSemControl.destSeq, nonzero, if_false]
          rw [clockEq, targetRun]
          simp [bad]
#print axioms compCorrectCallTail_path_bounded
#print axioms compCorrectJumpLower_path_bounded
#print axioms compCorrectRawCall_path_bounded
end InitECandidate.Runtime.StackRemove
