import InitECandidate.Runtime.RawCallExecutedSeq

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.IfCase
open InitECandidate.Runtime.StackToLab

abbrev ExecutedBranchIH {F : Type} (price : HolProg 64 → Nat)
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm 64)
    (truth : Bool) (program : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  ∀ left right,
    StackSemStateOps.getVar register source = some left →
    StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand) source = some right →
    wordSemWordCmp comparison left right = some truth →
    ExecutedProgramIH price program source

/-- Raw-call compilation preserves the selected branch and its local price.
Only the actually selected source branch supplies a recursive hypothesis. -/
theorem executed_if {F : Type} (price : HolProg 64 → Nat)
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm 64)
    (first second : HolProg 64) (info : Spt Nat)
    (samePrice : price (comp info (.ite comparison register operand first second)) =
      price (.ite comparison register operand first second))
    (source target post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (result : Option (StackSemResult 64))
    (firstIH : ExecutedBranchIH price comparison register operand true first source)
    (secondIH : ExecutedBranchIH price comparison register operand false second source)
    (hypothesis : StackSemEvaluate.evaluate (.ite comparison register operand first second, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    ExecutedSimulationResult price (comp info (.ite comparison register operand first second))
      info target post result
      (stackExecutionCost (fun p _ => price p) (.ite comparison register operand first second) source) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rw [StackSemEvaluate.evaluate_ite] at execution
  split at execution
  · rename_i left right leftRead rightRead
    split at execution
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, postRelation, targetRun, guard, cost⟩ :=
        firstIH left right leftRead rightRead compared info target post result
          ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, postRelation, ?_, guard, ?_⟩
      · rw [evaluateCompiledIf info source target relation]
        simp only [leftRead, rightRead, compared]
        exact targetRun
      · have localEq : price (.ite comparison register operand (comp info first) (comp info second)) =
            price (.ite comparison register operand first second) := samePrice
        simp only [comp, stackExecutionCost, selectedBranchBudget,
          getVar_targetClock info source target relation,
          getVarImm_targetClock info source target relation, leftRead, rightRead, compared]
        rw [localEq]
        exact Nat.add_le_add_left cost _
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, postRelation, targetRun, guard, cost⟩ :=
        secondIH left right leftRead rightRead compared info target post result
          ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, postRelation, ?_, guard, ?_⟩
      · rw [evaluateCompiledIf info source target relation]
        simp only [leftRead, rightRead, compared]
        exact targetRun
      · have localEq : price (.ite comparison register operand (comp info first) (comp info second)) =
            price (.ite comparison register operand first second) := samePrice
        simp only [comp, stackExecutionCost, selectedBranchBudget,
          getVar_targetClock info source target relation,
          getVarImm_targetClock info source target relation, leftRead, rightRead, compared]
        rw [localEq]
        exact Nat.add_le_add_left cost _
    · simp_all
  · simp_all

#print axioms executed_if
end InitECandidate.Runtime.StackRawCall
