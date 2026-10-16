import InitECandidate.Runtime.CrepStatementBudget
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Seq
namespace InitECandidate.Runtime
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Sequential composition follows the actual source intermediate state and adds
only the bounds of the two executions. Early termination uses the first bound. -/
theorem crep_seq_bounded {width : Nat} [NeZero width] {σ : Type}
    (first second : CrepProgHOL width) (source : CrepSemHOLState width σ)
    (firstBudget secondBudget : Nat)
    (ihSecond : ∀ firstResult firstState,
      (firstResult, firstState) = evalCrepSemHOLProgExact source first →
      firstResult = none → BoundedCrepPropertyAt second firstState secondBudget)
    (ihFirst : BoundedCrepPropertyAt first source firstBudget) :
    BoundedCrepPropertyAt (.seq first second) source (firstBudget + secondBudget) := by
  intro result sourceFinal target context live hEval hNotError hState hMem hGlobals hCode hLocals
  rw [evalCrepSemHOLProgExact_seq_holShape] at hEval
  cases hFirst : evalCrepSemHOLProgExact source first with
  | mk firstResult firstState =>
    rw [hFirst] at hEval
    cases firstResult with
    | none =>
      simp only at hEval
      obtain ⟨firstExtra, firstSmall, firstTargetResult, firstTargetFinal,
        hFirstRun, hFirstState, hFirstMem, hFirstGlobals, hFirstCode,
        hFirstResult, hFirstLocals⟩ :=
        ihFirst none firstState target context live hFirst (by simp)
          hState hMem hGlobals hCode hLocals
      have hFirstTargetNone : firstTargetResult = none := by
        simpa [resultToLoop] using hFirstResult
      subst firstTargetResult
      obtain ⟨secondExtra, secondSmall, finalTargetResult, finalTarget,
        hSecondRun, hSecondState, hSecondMem, hSecondGlobals, hSecondCode,
        hSecondResult, hSecondLocals⟩ :=
        (ihSecond none firstState hFirst.symm rfl)
          result sourceFinal firstTargetFinal context live hEval hNotError
          hFirstState hFirstMem hFirstGlobals hFirstCode hFirstLocals
      have hFirstRunLift :
          LoopSemStateFiniteExact.evaluate (compileHOLExact context live first)
            { target with clock := target.clock + (firstExtra + secondExtra) } =
              (none, { firstTargetFinal with
                clock := firstTargetFinal.clock + secondExtra }) := by
        have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
          (compileHOLExact context live first)
          { target with clock := target.clock + firstExtra } none firstTargetFinal
          secondExtra hFirstRun (by simp)
        simpa [Nat.add_assoc] using hLift
      refine ⟨firstExtra + secondExtra, by omega, finalTargetResult, finalTarget, ?_,
        hSecondState, hSecondMem, hSecondGlobals, hSecondCode,
        hSecondResult, hSecondLocals⟩
      rw [compileHOLExact, LoopSemStateFiniteExact.evaluate_seq, hFirstRunLift]
      exact hSecondRun
    | some firstValue =>
      have hFirstPair : (some firstValue, firstState) = (result, sourceFinal) := by
        simpa using hEval
      rcases Prod.mk.inj hFirstPair with ⟨hResultEq, hFinalEq⟩
      have hFirstNotError : some firstValue ≠ some .error := by
        intro h
        apply hNotError
        rw [← hResultEq]
        exact h
      obtain ⟨extra, small, targetResult, targetFinal,
        hRun, hFinalState, hFinalMem, hFinalGlobals, hFinalCode,
        hResultMap, hFinalLocals⟩ :=
        ihFirst (some firstValue) firstState target context live hFirst hFirstNotError
          hState hMem hGlobals hCode hLocals
      have hFinalState' : crepToLoopStateRelExact sourceFinal targetFinal :=
        hFinalEq ▸ hFinalState
      have hFinalMem' : crepToLoopMemRelHOLExact sourceFinal.memory
          targetFinal.memory sourceFinal.memaddrs := hFinalEq ▸ hFinalMem
      have hFinalGlobals' : crepToLoopGlobalsRelHOLExact sourceFinal.globals
          targetFinal.globals := hFinalEq ▸ hFinalGlobals
      have hFinalCode' : crepToLoopCodeRelExact context sourceFinal.code
          targetFinal.code := hFinalEq ▸ hFinalCode
      have hFinalLocals' : localsResultRel context live result sourceFinal targetFinal := by
        simpa [← hResultEq] using (hFinalEq ▸ hFinalLocals)
      have hTargetSome : targetResult ≠ none := by
        rw [hResultMap]
        cases firstValue <;> simp [resultToLoop]
      have hResultMap' : targetResult = resultToLoop result := by
        simpa [← hResultEq] using hResultMap
      refine ⟨extra, by omega, targetResult, targetFinal, ?_, hFinalState', hFinalMem',
        hFinalGlobals', hFinalCode', hResultMap', hFinalLocals'⟩
      rw [compileHOLExact, LoopSemStateFiniteExact.evaluate_seq, hRun]
      cases targetResult with
      | none => exact False.elim (hTargetSome rfl)
      | some value => rfl
/-- Uniform syntax certificate for straight-line source statement compilation. -/
def CrepStaticFuel {width : Nat} [NeZero width] (p : CrepProgHOL width) (cost : Nat) : Prop :=
  ∀ ctxt live, loopExprFuel (compileHOLExact ctxt live p) = some cost

theorem crep_static_ite {width : Nat} [NeZero width]
    (e : CrepExpHOL width) (yes no : CrepProgHOL width) (a b : Nat)
    (ha : CrepStaticFuel yes a) (hb : CrepStaticFuel no b) :
    CrepStaticFuel (.ite e yes no) (crepExprFuel e + (a + b + 1)) := by
  intro ctxt live
  rcases compiled : compileExpHOLExact ctxt (ctxt.vmax + 1) live e with ⟨code,value,next,out⟩
  have first := compileExp_fuel ctxt (ctxt.vmax + 1) live e
  rw [compiled] at first
  have tail : loopExprFuel (loopNestedSeqHOL
      [.assign next value, .ite .notEqual next (.imm (0 : BitVec width))
        (compileHOLExact ctxt live yes) (compileHOLExact ctxt live no) live]) = some (a + b + 1) := by
    simp [loopNestedSeqHOL,loopExprFuel,ha ctxt live,hb ctxt live]
  have full := loopExprFuel_append code _ _ _ first tail
  simpa [compileHOLExact,compiled] using full

theorem crep_static_ite_bounded {width : Nat} [NeZero width] {F : Type}
    (e : CrepExpHOL width) (yes no : CrepProgHOL width) (a b : Nat)
    (ha : CrepStaticFuel yes a) (hb : CrepStaticFuel no b) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.ite e yes no) s (crepExprFuel e + (a + b + 1)) :=
  crep_statement_of_static _ _ _ (fun ctxt live =>
    ⟨_,Nat.le_refl _,crep_static_ite e yes no a b ha hb ctxt live⟩)

theorem crep_static_dec {width : Nat} [NeZero width]
    (name : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (cost : Nat)
    (hbody : CrepStaticFuel body cost) :
    CrepStaticFuel (.dec name e body) (crepExprFuel e + cost) := by
  intro ctxt live
  rcases compiled : compileExpHOLExact ctxt (ctxt.vmax + 1) live e with ⟨code,value,next,out⟩
  have first := compileExp_fuel ctxt (ctxt.vmax + 1) live e
  rw [compiled] at first
  simp only [compileHOLExact,compiled]
  simp only [loopExprFuel,first]
  rw [hbody _ _]
  simp

theorem crep_static_dec_bounded {width : Nat} [NeZero width] {F : Type}
    (name : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width) (cost : Nat)
    (hbody : CrepStaticFuel body cost) (s : CrepSemHOLState width F) :
    BoundedCrepPropertyAt (.dec name e body) s (crepExprFuel e + cost) :=
  crep_statement_of_static _ _ _ (fun ctxt live =>
    ⟨_,Nat.le_refl _,crep_static_dec name e body cost hbody ctxt live⟩)

#print axioms crep_static_dec
#print axioms crep_static_dec_bounded
#print axioms crep_static_ite
#print axioms crep_static_ite_bounded
#print axioms crep_seq_bounded
end InitECandidate.Runtime
