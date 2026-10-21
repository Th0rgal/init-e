import InitECandidate.Runtime.StackRefinedRemovalLeaves
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- A leaf can reuse its original semantic witness under cheaper target
prices and a proved local source price. Recursive nodes use structural IHs. -/
theorem removalCostSimulation_repriceLeaf {F : Type}
    (oldSource newSource oldTarget newTarget : HolProg 64 → Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : removalSupported p = true) (leaf : removalLeaf p = true)
    (simulation : RemovalCostSimulationFor oldSource oldTarget jump bounds p source)
    (targetCheaper : ∀ q, newTarget q ≤ oldTarget q)
    (sourceBound : oldSource p ≤ newSource p) :
    RemovalCostSimulationFor newSource newTarget jump bounds p source := by
  intro post target result pointer premises
  obtain ⟨clock, final, run, relation, cost⟩ := simulation post target result pointer premises
  refine ⟨clock, final, run, relation, ?_⟩
  have smaller := stackExecutionCost_mono (fun p _ => newTarget p) (fun p _ => oldTarget p)
    (fun p _ => targetCheaper p) (StackRemove.comp jump bounds pointer p)
    {target with clock := clock+target.clock}
  rw [stackExecutionCost_supported_removalLeaf _ p supported leaf] at cost ⊢
  exact smaller.trans (cost.trans sourceBound)

theorem refinedRemovalLocalPrice_atomic (gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (atomic : executionAtomic p = true) :
    refinedRemovalLocalPrice gap bounds p = refinedNativePriceWithGap gap p := by
  cases p <;> simp only [executionAtomic, Bool.false_eq_true] at atomic
  all_goals rfl

/-- Closed refined pricing for every supported nonrecursive source node.
The newly tightened direct operations use six at gap six; complex frame
operations reuse their original conservative proofs under cheaper targets. -/
theorem refinedRemovalCostSimulation_leaf {F : Type} (gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : removalSupported p = true) (leaf : removalLeaf p = true) :
    RemovalCostSimulationFor (refinedRemovalLocalPrice gap bounds) (refinedNativePriceWithGap gap)
      false bounds p source := by
  by_cases atomic : executionAtomic p = true
  · apply removalCostSimulation_atomic_refined _ gap false bounds p atomic _ source
    rw [refinedRemovalLocalPrice_atomic gap bounds p atomic]
  · cases p <;> try (solve | simp [executionAtomic] at atomic)
    all_goals try (solve | simp [removalLeaf] at leaf)
    all_goals try (solve | simp [removalSupported, executionAtomic] at supported)
    case get reg name => exact removalCostSimulation_get_refined _ gap false bounds reg name (Nat.le_refl _) source
    case set name reg => exact removalCostSimulation_set_refined _ gap false bounds reg name (Nat.le_refl _) source
    case opCurrHeap op dst input => exact removalCostSimulation_opCurrHeap_refined _ gap false bounds op dst input (Nat.le_refl _) source
    case stackLoad reg count =>
      by_cases fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true
      · apply removalCostSimulation_stackLoad_fast_refined _ gap false bounds reg count fast _ source
        simp only [refinedRemovalLocalPrice, fast, ↓reduceIte, Nat.le_refl]
      · apply removalCostSimulation_repriceLeaf (removalLocalPrice gap bounds) _ (nativePriceWithGap gap) _ false bounds
          (.stackLoad reg count) source supported leaf
          (removalCostSimulation_leaf gap bounds _ source supported leaf) (refinedNativePriceWithGap_le gap)
        simp only [refinedRemovalLocalPrice, if_neg fast, Nat.le_refl]
    case stackStore reg count =>
      by_cases fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true
      · apply removalCostSimulation_stackStore_fast_refined _ gap false bounds reg count fast _ source
        simp only [refinedRemovalLocalPrice, fast, ↓reduceIte, Nat.le_refl]
      · apply removalCostSimulation_repriceLeaf (removalLocalPrice gap bounds) _ (nativePriceWithGap gap) _ false bounds
          (.stackStore reg count) source supported leaf
          (removalCostSimulation_leaf gap bounds _ source supported leaf) (refinedNativePriceWithGap_le gap)
        simp only [refinedRemovalLocalPrice, if_neg fast, Nat.le_refl]
    all_goals apply removalCostSimulation_repriceLeaf (removalLocalPrice gap bounds) _ (nativePriceWithGap gap) _ false bounds _ source supported leaf (removalCostSimulation_leaf gap bounds _ source supported leaf) (refinedNativePriceWithGap_le gap)
    all_goals exact Nat.le_refl _

#print axioms removalCostSimulation_repriceLeaf
#print axioms refinedRemovalLocalPrice_atomic
#print axioms refinedRemovalCostSimulation_leaf
end InitECandidate.Runtime.StackToLab
