import InitECandidate.Runtime.StackExecutionNativeIfExit
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- The complete normal conditional cost rule, independent of static arm layout. -/
theorem normalExecutionCost_if {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64) (choice : Bool)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some choice)
    (runKind : (StackSemEvaluate.evaluate ((if choice then yes else no), source)).1 = none)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : NormalWeightedFlatten (if choice then yes else no) source
      (executionCostPrice price (if choice then yes else no) source)) :
    NormalWeightedFlatten (.ite cmp reg operand yes no) source
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  cases choice with
  | false => exact normalExecutionCost_if_false price yes no cmp reg operand source x y lhs rhs chosen runKind localPrice bodyBound
  | true => exact normalExecutionCost_if_true price yes no cmp reg operand source x y lhs rhs chosen runKind localPrice bodyBound

/-- The complete exit conditional cost rule, independent of static arm layout. -/
theorem exitExecutionCost_if {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64) (choice : Bool)
    (result : StackSemResult 64)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some choice)
    (runKind : (StackSemEvaluate.evaluate ((if choice then yes else no), source)).1 = some result)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : ExitWeightedFlatten (if choice then yes else no) source result
      (executionCostPrice price (if choice then yes else no) source)) :
    ExitWeightedFlatten (.ite cmp reg operand yes no) source result
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  cases choice with
  | false => exact exitExecutionCost_if_false price yes no cmp reg operand source x y lhs rhs result chosen runKind localPrice bodyBound
  | true => exact exitExecutionCost_if_true price yes no cmp reg operand source x y lhs rhs result chosen runKind localPrice bodyBound

/-- The complete terminal conditional cost rule, independent of static arm layout. -/
theorem terminalExecutionCost_if {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (yes no : HolProg 64) (cmp : HolCmp) (reg : Nat) (operand : HolRegImm 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (x y : WordLocW 64) (choice : Bool)
    (result : StackSemResult 64) (outcome : HolOutcome)
    (lhs : StackSemStateOps.getVar reg source = some x)
    (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
    (chosen : wordSemWordCmp cmp x y = some choice)
    (runKind : (StackSemEvaluate.evaluate ((if choice then yes else no), source)).1 = some result)
    (localPrice : ∀ encoded pc, LabToTarget.controlWork 3 encoded pc + 2 ≤
      price (.ite cmp reg operand yes no) source encoded)
    (bodyBound : TerminalWeightedFlatten (if choice then yes else no) source result outcome
      (executionCostPrice price (if choice then yes else no) source)) :
    TerminalWeightedFlatten (.ite cmp reg operand yes no) source result outcome
      (executionCostPrice price (.ite cmp reg operand yes no) source) := by
  cases choice with
  | false => exact terminalExecutionCost_if_false price yes no cmp reg operand source x y lhs rhs result outcome chosen runKind localPrice bodyBound
  | true => exact terminalExecutionCost_if_true price yes no cmp reg operand source x y lhs rhs result outcome chosen runKind localPrice bodyBound

#print axioms normalExecutionCost_if
#print axioms exitExecutionCost_if
#print axioms terminalExecutionCost_if
end InitECandidate.Runtime.StackToLab
