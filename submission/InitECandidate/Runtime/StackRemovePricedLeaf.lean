import InitECandidate.Runtime.StackRemovalLeafSimulation
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Every supported nonrecursive source node pays only its local price.
The support guard excludes jumpLower, whose counter may enter another body. -/
theorem stackExecutionCost_supported_removalLeaf {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → Nat)
    (p : HolProg 64) (supported : removalSupported p = true) (leaf : removalLeaf p = true)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost price p source = price p source := by
  cases p <;> simp only [removalLeaf, Bool.false_eq_true] at leaf
  all_goals try (solve | simp [removalSupported, executionAtomic] at supported)
  all_goals simp [stackExecutionCost]

/-- Attach a local compiled-fragment bound to the original semantic theorem.
Only supported leaf syntax is accepted; recursive budgets use separate IHs. -/
theorem removalCostSimulation_fragmentWithPrice {F : Type}
    (sourcePrice targetPrice : HolProg 64 → Nat) (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (supported : removalSupported p = true) (leaf : removalLeaf p = true)
    (fragment : ∀ pointer (target : StackSemStateFiniteExact 64 LabToTarget.Config F),
      stackExecutionCost (fun p _ => targetPrice p) (StackRemove.comp jump bounds pointer p) target ≤ sourcePrice p)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulationFor sourcePrice targetPrice jump bounds p source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.Assembly.compCorrect p source result post target pointer bounds jump premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · rw [stackExecutionCost_supported_removalLeaf _ p supported leaf]
    exact fragment pointer _

#print axioms stackExecutionCost_supported_removalLeaf
#print axioms removalCostSimulation_fragmentWithPrice
end InitECandidate.Runtime.StackToLab
