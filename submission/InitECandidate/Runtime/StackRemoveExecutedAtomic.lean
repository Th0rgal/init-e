import InitECandidate.Runtime.StackRemoveExecutedSimulation
import InitECandidate.Runtime.StackExecutionEligibility
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Atomic post-removal operations are unchanged by stack removal. -/
theorem removal_comp_atomic (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat)
    (p : HolProg 64) (atomic : executionAtomic p = true) : StackRemove.comp jump bounds pointer p = p := by
  cases p <;> simp only [executionAtomic, Bool.false_eq_true] at atomic
  all_goals simp [StackRemove.comp]

theorem stackExecutionCost_atomic {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → Nat)
    (p : HolProg 64) (atomic : executionAtomic p = true)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : stackExecutionCost price p source = price p source := by
  cases p <;> simp only [executionAtomic, Bool.false_eq_true] at atomic
  all_goals simp [stackExecutionCost]

/-- Quantitative simulation for every unchanged atomic constructor. The
semantic compiler theorem derives the target run; local instruction pricing
supplies its executed-cost bound independently. -/
theorem removalCostSimulation_atomic {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (p : HolProg 64) (atomic : executionAtomic p = true)
    (localBound : nativePriceWithGap gap p ≤ sourcePrice p)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap jump bounds p source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.Assembly.compCorrect p source result post target pointer bounds jump premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · rw [removal_comp_atomic jump bounds pointer p atomic,
      stackExecutionCost_atomic _ p atomic, stackExecutionCost_atomic _ p atomic]
    exact localBound

#print axioms removalCostSimulation_atomic
end InitECandidate.Runtime.StackToLab
