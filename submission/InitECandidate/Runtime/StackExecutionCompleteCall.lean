import InitECandidate.Runtime.StackExecutionCompleteCallEntry
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem executionComplete_call {F : Type} (rp : HolProg 64) (link l1 l2 : Nat)
    (dest : Sum Nat Nat) (handler : Option (HolProg 64 × Nat × Nat))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (ih : ExecutionCompleteIH (.call (some (rp, link, l1, l2)) dest handler) source) :
    ExecutionCompleteAt (.call (some (rp, link, l1, l2)) dest handler) source := by
  intro result post run valid supported global scope
  have rootRun := run
  rw [StackSemEvaluate.evaluate_call] at run
  dsimp only at run
  cases found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none =>
    simp only [found] at run
    obtain ⟨rfl, _⟩ := Prod.mk.inj run
    exact False.elim valid
  | some prog =>
    simp only [found] at run
    by_cases zero : source.clock = 0
    · rw [if_pos zero] at run
      obtain ⟨rfl, _⟩ := Prod.mk.inj run
      exact False.elim valid
    · rw [if_neg zero, StackSemEvaluateClock.fixClockEvaluate] at run
      rcases bodyRun : StackSemEvaluate.evaluate (prog,
          StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source)) with ⟨bodyResult, middle⟩
      rw [bodyRun] at run
      cases bodyResult with
      | none =>
        obtain ⟨rfl, _⟩ := Prod.mk.inj run
        exact False.elim valid
      | some value =>
        cases value with
        | result value =>
          dsimp only at run
          by_cases wrong : value ≠ .loc l1 l2
          · rw [if_pos wrong] at run
            obtain ⟨rfl, _⟩ := Prod.mk.inj run
            exact False.elim valid
          · have eq : value = .loc l1 l2 := Classical.not_not.mp wrong
            subst value
            rw [if_neg (not_not_intro rfl)] at run
            have tree := executionComplete_call_body ih zero found global bodyRun scope.return_label
            have rest := executionComplete_call_continuation ih zero tree global scope.return_body
              (executionSupported_return supported) valid run
            exact ExecutionTrace.callReturn
              (by simpa only [executionKindOfResult_result] using rootRun) zero found tree rest
        | exception value =>
          cases handler with
          | none =>
            dsimp only at run
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
            have tree := executionComplete_call_body ih zero found global bodyRun valid
            exact ExecutionTrace.callExit rootRun zero found (by simp [callResultPropagates]) tree
          | some packet =>
            rcases packet with ⟨hp, hs, hl⟩
            dsimp only at run
            by_cases wrong : value ≠ .loc hs hl
            · rw [if_pos wrong] at run
              obtain ⟨rfl, _⟩ := Prod.mk.inj run
              exact False.elim valid
            · have eq : value = .loc hs hl := Classical.not_not.mp wrong
              subst value
              rw [if_neg (not_not_intro rfl)] at run
              have tree := executionComplete_call_body ih zero found global bodyRun scope.handler_label
              have rest := executionComplete_call_continuation ih zero tree global scope.handler_body
                (executionSupported_handler supported) valid run
              exact ExecutionTrace.callHandler
                (by simpa only [executionKindOfResult_result] using rootRun) zero found tree rest
        | «break» label | «continue» label | error | timeOut =>
          dsimp only at run
          obtain ⟨rfl, _⟩ := Prod.mk.inj run
          exact False.elim valid
        | halt value =>
          dsimp only at run
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
          cases value with
          | loc _ _ => exact False.elim valid
          | word value =>
            have tree := executionComplete_call_body ih zero found global bodyRun valid
            exact ExecutionTrace.callFinal rootRun zero found (by simp [callResultPropagates]) tree
        | finalFFI event =>
          dsimp only at run
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
          have tree := executionComplete_call_body ih zero found global bodyRun valid
          exact ExecutionTrace.callFinal rootRun zero found (by simp [callResultPropagates]) tree

#print axioms executionComplete_call
end InitECandidate.Runtime.StackToLab
