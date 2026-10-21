import InitECandidate.Runtime.StackExecutionNativeBasis
import InitECandidate.Runtime.StackWeightedCallTerminal
import InitECandidate.Runtime.StackWeightedCallExit
import InitECandidate.Runtime.StackWeightedRawCall
import InitECandidate.Runtime.StackWeightedRawCallExit
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- Actual tail-call executed cost supplies its native exit budget. -/
theorem exitExecutionCost_call_tail {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (dest : Nat ⊕ Nat) (prog : HolProg 64)
    (result : StackSemResult 64)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest source.regs source.code = some prog)
    (localPrice : ∀ encoded, callJumpWork dest ≤ price (.call none dest none) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock source) result
      (executionCostPrice price prog (StackSemStateOps.decClock source))) :
    ExitWeightedFlatten (.call none dest none) source result (executionCostPrice price (.call none dest none) source) := by
  apply (exitWeightedFlatten_call_tail source dest prog result
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock source) encoded 0)
    positive found bodyBound).mono
  intro encoded pc
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_6]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, positive, if_neg, found]
  have h := localPrice encoded
  omega

/-- Actual tail-call executed cost supplies its native terminal budget. -/
theorem terminalExecutionCost_call_tail {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (dest : Nat ⊕ Nat) (prog : HolProg 64)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (positive : source.clock ≠ 0)
    (found : StackSemControl.findCode dest source.regs source.code = some prog)
    (localPrice : ∀ encoded, callJumpWork dest ≤ price (.call none dest none) source encoded)
    (bodyBound : TerminalWeightedFlatten prog (StackSemStateOps.decClock source) result outcome
      (executionCostPrice price prog (StackSemStateOps.decClock source))) :
    TerminalWeightedFlatten (.call none dest none) source result outcome (executionCostPrice price (.call none dest none) source) := by
  apply (terminalWeightedFlatten_call_tail source dest prog result outcome
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock source) encoded 0)
    positive found bodyBound).mono
  intro encoded pc
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_6]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, positive, if_neg, found]
  have h := localPrice encoded
  omega

/-- Actual raw-call executed cost supplies its native exit budget. -/
theorem exitExecutionCost_call_raw {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (dest : Nat) (prologue prog : HolProg 64)
    (result : StackSemResult 64)
    (positive : source.clock ≠ 0)
    (found : sptLookup dest source.code = some (.seq prologue prog))
    (localPrice : ∀ encoded, 2 ≤ price (.rawCall dest) source encoded)
    (bodyBound : ExitWeightedFlatten prog (StackSemStateOps.decClock source) result
      (executionCostPrice price prog (StackSemStateOps.decClock source))) :
    ExitWeightedFlatten (.rawCall dest) source result (executionCostPrice price (.rawCall dest) source) := by
  apply (exitWeightedFlatten_rawCall source dest prologue prog result
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock source) encoded 0)
    positive found bodyBound).mono
  intro encoded pc
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_5]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, positive, if_neg, found]
  have h := localPrice encoded
  omega

/-- Actual raw-call executed cost supplies its native terminal budget. -/
theorem terminalExecutionCost_call_raw {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (dest : Nat) (prologue prog : HolProg 64)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (positive : source.clock ≠ 0)
    (found : sptLookup dest source.code = some (.seq prologue prog))
    (localPrice : ∀ encoded, 2 ≤ price (.rawCall dest) source encoded)
    (bodyBound : TerminalWeightedFlatten prog (StackSemStateOps.decClock source) result outcome
      (executionCostPrice price prog (StackSemStateOps.decClock source))) :
    TerminalWeightedFlatten (.rawCall dest) source result outcome (executionCostPrice price (.rawCall dest) source) := by
  apply (terminalWeightedFlatten_rawCall source dest prologue prog result outcome
    (fun encoded => executionCostPrice price prog (StackSemStateOps.decClock source) encoded 0)
    positive found bodyBound).mono
  intro encoded pc
  simp only [executionCostPrice]
  rw [stackExecutionCost.eq_5]
  simp only [Option.isSome_none, Bool.false_eq_true, if_false, positive, if_neg, found]
  have h := localPrice encoded
  omega

#print axioms exitExecutionCost_call_tail
#print axioms terminalExecutionCost_call_tail
#print axioms exitExecutionCost_call_raw
#print axioms terminalExecutionCost_call_raw
end InitECandidate.Runtime.StackToLab
