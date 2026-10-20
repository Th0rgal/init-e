import InitECandidate.Runtime.StackExecutionNativeReturn
import InitECandidate.Runtime.StackWeightedCallPropagate
import InitECandidate.Runtime.StackWeightedCallPropagateExit
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

private theorem selectedBudget_zero (result : StackSemResult 64)
    (handler : Option (HolProg 64 × Nat × Nat)) (l1 l2 first second : Nat)
    (propagates : callResultPropagates result handler) :
    selectedContinuationBudget (some result) l1 l2 handler first second = 0 := by
  cases handler <;> cases result <;> simp_all [callResultPropagates, selectedContinuationBudget]

/-- Executed cost for a propagated exit callee includes no continuation. -/
theorem exitExecutionCost_call_propagate {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (result : StackSemResult 64)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some result, bodyPost))
    (propagates : callResultPropagates result handler)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 2 encoded pc + callJumpWork dest ≤
      price (.call (some (returnProg, link, l1, l2)) dest handler) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) result
      (executionCostPrice price prog (StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)))) :
    ExitWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest handler) source result
      (executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest handler) source) := by
  apply (exitWeightedFlatten_call_propagate source bodyPost returnProg prog link l1 l2 dest handler result
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
    positive found bodyRun propagates bodyBound).mono
  intro encoded pc
  rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest handler _
    positive found bodyRun encoded pc]
  rw [selectedBudget_zero result handler l1 l2 _ _ propagates]
  have h := localPrice encoded pc
  dsimp only [executionCostPrice] at h ⊢
  omega

/-- Executed cost for a propagated terminal callee includes no continuation. -/
theorem terminalExecutionCost_call_propagate {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source bodyPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (returnProg prog : HolProg 64) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg 64 × Nat × Nat))
    (result : StackSemResult 64) (outcome : HolOutcome)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
    (bodyRun : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) = (some result, bodyPost))
    (propagates : callResultPropagates result handler)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 2 encoded pc + callJumpWork dest ≤
      price (.call (some (returnProg, link, l1, l2)) dest handler) source encoded)
    (bodyBound : TerminalWeightedFlatten prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) result outcome
      (executionCostPrice price prog (StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) source)))) :
    TerminalWeightedFlatten (.call (some (returnProg, link, l1, l2)) dest handler) source result outcome
      (executionCostPrice price (.call (some (returnProg, link, l1, l2)) dest handler) source) := by
  apply (terminalWeightedFlatten_call_propagate source bodyPost returnProg prog link l1 l2 dest handler result outcome
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) source)) encoded 0)
    positive found bodyRun propagates bodyBound).mono
  intro encoded pc
  rw [executionCostPrice_call price source bodyPost returnProg prog link l1 l2 dest handler _
    positive found bodyRun encoded pc]
  rw [selectedBudget_zero result handler l1 l2 _ _ propagates]
  have h := localPrice encoded pc
  dsimp only [executionCostPrice] at h ⊢
  omega

#print axioms exitExecutionCost_call_propagate
#print axioms terminalExecutionCost_call_propagate
end InitECandidate.Runtime.StackToLab
