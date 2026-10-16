import InitECandidate.Runtime.RawCallBudget

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.IfCase

/-- Returning or tail calls reserve their own consumed tick to pay for a
possible enclosing tail-call optimization. Other syntax can use all consumed fuel. -/
def clockAllowance {width : Nat} [NeZero width] (program : HolProg width)
    (before after : Nat) : Nat :=
  before - after - (match program with | .call _ _ _ => 1 | _ => 0)

theorem clockAllowance_le {width : Nat} [NeZero width] (program : HolProg width)
    (before after : Nat) : clockAllowance program before after ≤ before - after :=
  Nat.sub_le _ _

/-- Recursive budget charged to actual source clock consumption. -/
abbrev ProgramIH {width : Nat} [NeZero width] (C F : Type) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target →
    BoundedSimulationResult (comp info program) info target post result (clockAllowance program source.clock post.clock)

abbrev BranchIH {width : Nat} [NeZero width] (C F : Type)
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm width)
    (truth : Bool) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (left right : WordLocW width),
    StackSemStateOps.getVar register source = some left →
    StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand)
      source = some right →
    wordSemWordCmp comparison left right = some truth →
    ProgramIH C F program source

theorem compCorrectIf {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm width)
    (first second : HolProg width)
    (info : Spt Nat) (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : BranchIH C F comparison register operand true first source)
    (secondIH : BranchIH C F comparison register operand false second source)
    (hypothesis : StackSemEvaluate.evaluate (.ite comparison register operand first second, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.ite comparison register operand first second))
      info target resultState result (source.clock - resultState.clock) ∧
    BoundedSimulationResult (comp info (.ite comparison register operand first second))
      info target resultState result (source.clock - resultState.clock) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have same : compTop info (.ite comparison register operand first second) =
      comp info (.ite comparison register operand first second) := rfl
  rw [same]
  suffices simulation : BoundedSimulationResult
      (comp info (.ite comparison register operand first second)) info target resultState result
        (source.clock - resultState.clock) by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_ite] at execution
  split at execution
  · rename_i left right leftRead rightRead
    split at execution
    · rename_i compared
      obtain ⟨clock, clockBound, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
        firstIH left right leftRead rightRead compared
          info target resultState result ⟨execution, nonerror, relation⟩
      refine ⟨clock, Nat.le_trans clockBound (clockAllowance_le _ _ _), targetState,
        stackSpace, postRelation, ?_, guard⟩
      rw [evaluateCompiledIf info source target relation]
      simp_all
    · rename_i compared
      obtain ⟨clock, clockBound, targetState, stackSpace, postRelation, targetExecution, guard⟩ :=
        secondIH left right leftRead rightRead compared
          info target resultState result ⟨execution, nonerror, relation⟩
      refine ⟨clock, Nat.le_trans clockBound (clockAllowance_le _ _ _), targetState,
        stackSpace, postRelation, ?_, guard⟩
      rw [evaluateCompiledIf info source target relation]
      simp_all
    · simp_all
  · simp_all


#print axioms compCorrectIf
end InitECandidate.Runtime.StackRawCall
