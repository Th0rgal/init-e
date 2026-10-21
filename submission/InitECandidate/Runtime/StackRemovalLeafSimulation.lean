import InitECandidate.Runtime.StackRemovalLocalPrice
import InitECandidate.Runtime.StackRemovalEligibility
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

def removalLeaf : HolProg 64 → Bool
  | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .call _ _ _ | .rawCall _ => false
  | _ => true

theorem removalLocalPrice_atomic (gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (atomic : executionAtomic p = true) : removalLocalPrice gap bounds p = nativePriceWithGap gap p := by
  cases p <;> simp only [executionAtomic, Bool.false_eq_true] at atomic
  all_goals rfl

/-- All nonrecursive source constructors present in the guest have a genuine
quantitative simulation under the fixed, size-sensitive local price. -/
theorem removalCostSimulation_leaf {F : Type} (gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : removalSupported p = true) (leaf : removalLeaf p = true) :
    RemovalCostSimulation (removalLocalPrice gap bounds) gap false bounds p source := by
  by_cases atomic : executionAtomic p = true
  · exact removalCostSimulation_atomic _ gap false bounds p atomic
      (by rw [removalLocalPrice_atomic gap bounds p atomic]) source
  · cases p <;> try (solve | simp [executionAtomic] at atomic)
    all_goals try (solve | simp [removalLeaf] at leaf)
    all_goals try (solve | simp [removalSupported, executionAtomic] at supported)
    case get reg name => exact removalCostSimulation_get _ gap false bounds reg name (Nat.le_refl _) source
    case set name reg => exact removalCostSimulation_set _ gap false bounds reg name (Nat.le_refl _) source
    case opCurrHeap op dest input => exact removalCostSimulation_opCurrHeap _ gap false bounds op dest input (Nat.le_refl _) source
    case stackGetSize reg => exact removalCostSimulation_stackGetSize _ gap false bounds reg (Nat.le_refl _) source
    case stackSetSize reg => exact removalCostSimulation_stackSetSize _ gap false bounds reg (Nat.le_refl _) source
    case stackAlloc count => exact removalCostSimulation_stackAlloc _ gap count bounds (Nat.le_refl _) source
    case stackFree count => exact removalCostSimulation_stackFree _ gap false bounds count (Nat.le_refl _) source
    case stackLoad reg count =>
      by_cases fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true
      · apply removalCostSimulation_stackLoad_fast _ gap false bounds reg count fast _ source
        simp [removalLocalPrice, fast]
      · apply removalCostSimulation_stackLoad _ gap false bounds reg count _ source
        simp [removalLocalPrice, fast]
    case stackStore reg count =>
      by_cases fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true
      · apply removalCostSimulation_stackStore_fast _ gap false bounds reg count fast _ source
        simp [removalLocalPrice, fast]
      · apply removalCostSimulation_stackStore _ gap false bounds reg count _ source
        simp [removalLocalPrice, fast]

#print axioms removalCostSimulation_leaf
end InitECandidate.Runtime.StackToLab
