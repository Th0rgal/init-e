import InitECandidate.Runtime.StackReturningCallRunCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

/-- A non-return callee outcome propagates without executing a return
continuation. In particular, exceptions without a handler pay no return copies. -/
theorem stackCost_returning_call_propagate {F : Type}
    (callee continuation : HolProg 64) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (source post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64)) (bodyClock bodyBudget : Nat)
    (nonzero : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some callee)
    (notReturn : ∀ value, result ≠ some (.result value))
    (run : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
        clock := (StackSemStateOps.decClock source).clock + bodyClock}) = (result, post))
    (bodyCost : stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      callee {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
        clock := (StackSemStateOps.decClock source).clock + bodyClock} ≤ bodyBudget) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (.call (some (continuation,link,l1,l2)) dest none)
      {source with clock := source.clock + bodyClock} ≤ bodyBudget + 12 := by
  let entry : StackSemStateFiniteExact 64 LabToTarget.Config F :=
    {StackSemStateOps.setVar link (.loc l1 l2) (StackSemStateOps.decClock source) with
      clock := (StackSemStateOps.decClock source).clock + bodyClock}
  have actualEntry : StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2)
      {source with clock := source.clock + bodyClock}) = entry := by
    simp only [entry, StackSemStateOps.decClock, StackSemStateOps.setVar]
    congr 1
    omega
  have selectedZero : ∀ returnBudget handlerBudget,
      selectedContinuationBudget result l1 l2 none returnBudget handlerBudget = 0 := by
    intro returnBudget handlerBudget
    cases result with
    | none => rfl
    | some outcome => cases outcome <;> simp_all [selectedContinuationBudget]
  have bound := stackCost_returning_call_run continuation link l1 l2 dest none callee
    {source with clock := source.clock + bodyClock} post result
    (by simp only; omega) found (by rw [actualEntry]; exact run)
  rw [actualEntry] at bound
  simp only [selectedZero, Nat.add_zero] at bound
  change stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p) callee entry ≤ bodyBudget at bodyCost
  exact bound.trans (Nat.add_le_add_right bodyCost 12)

#print axioms stackCost_returning_call_propagate
end InitECandidate.Runtime.StackToLab
