import InitECandidate.Runtime.StackRemovePricedLeaf
import InitECandidate.Runtime.StackRefinedRemovalPrice
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- A global/store-field access compiles to one move or memory instruction. -/
theorem removalCostSimulation_get_refined {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register : Nat) (name : StoreName)
    (localBound : 1+(gap-1) ≤ sourcePrice (.get register name))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulationFor sourcePrice (refinedNativePriceWithGap gap) jump bounds (.get register name) source := by
  apply removalCostSimulation_fragmentWithPrice sourcePrice (refinedNativePriceWithGap gap) jump bounds
    (.get register name) (by simp only [removalSupported]) (by rfl) _ source
  intro pointer target
  rw [StackRemove.comp]
  split <;> simpa only [moveInst, moveHOL, stackExecutionCost, refinedNativePriceWithGap, instLocalCost] using localBound

/-- A global/store-field access compiles to one move or memory instruction. -/
theorem removalCostSimulation_set_refined {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register : Nat) (name : StoreName)
    (localBound : 1+(gap-1) ≤ sourcePrice (.set name register))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulationFor sourcePrice (refinedNativePriceWithGap gap) jump bounds (.set name register) source := by
  apply removalCostSimulation_fragmentWithPrice sourcePrice (refinedNativePriceWithGap gap) jump bounds
    (.set name register) (by simp only [removalSupported]) (by rfl) _ source
  intro pointer target
  rw [StackRemove.comp]
  split <;> simpa only [moveInst, moveHOL, stackExecutionCost, refinedNativePriceWithGap, instLocalCost] using localBound

theorem removalCostSimulation_opCurrHeap_refined {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (op : BinOp) (destination input : Nat)
    (localBound : 1+(gap-1) ≤ sourcePrice (.opCurrHeap op destination input))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulationFor sourcePrice (refinedNativePriceWithGap gap) jump bounds (.opCurrHeap op destination input) source := by
  apply removalCostSimulation_fragmentWithPrice sourcePrice (refinedNativePriceWithGap gap) jump bounds
    (.opCurrHeap op destination input) (by simp only [removalSupported]) (by rfl) _ source
  intro pointer target
  simpa only [StackRemove.comp, stackExecutionCost, refinedNativePriceWithGap, instLocalCost] using localBound

theorem removalCostSimulation_stackLoad_fast_refined {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register count : Nat)
    (fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true)
    (localBound : 1+(gap-1) ≤ sourcePrice (.stackLoad register count))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulationFor sourcePrice (refinedNativePriceWithGap gap) jump bounds (.stackLoad register count) source := by
  apply removalCostSimulation_fragmentWithPrice sourcePrice (refinedNativePriceWithGap gap) jump bounds
    (.stackLoad register count) (by simp only [removalSupported]) (by rfl) _ source
  intro pointer target
  simpa only [StackRemove.comp, fast, ↓reduceIte, stackExecutionCost, refinedNativePriceWithGap, instLocalCost] using localBound

theorem removalCostSimulation_stackStore_fast_refined {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register count : Nat)
    (fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true)
    (localBound : 1+(gap-1) ≤ sourcePrice (.stackStore register count))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulationFor sourcePrice (refinedNativePriceWithGap gap) jump bounds (.stackStore register count) source := by
  apply removalCostSimulation_fragmentWithPrice sourcePrice (refinedNativePriceWithGap gap) jump bounds
    (.stackStore register count) (by simp only [removalSupported]) (by rfl) _ source
  intro pointer target
  simpa only [StackRemove.comp, fast, ↓reduceIte, stackExecutionCost, refinedNativePriceWithGap, instLocalCost] using localBound

theorem removalCostSimulation_atomic_refined {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (p : HolProg 64) (atomic : executionAtomic p = true)
    (localBound : refinedNativePriceWithGap gap p ≤ sourcePrice p)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulationFor sourcePrice (refinedNativePriceWithGap gap) jump bounds p source :=
  removalCostSimulation_atomicWithPrice sourcePrice (refinedNativePriceWithGap gap) jump bounds p atomic localBound source

#print axioms removalCostSimulation_get_refined
#print axioms removalCostSimulation_set_refined
#print axioms removalCostSimulation_opCurrHeap_refined
#print axioms removalCostSimulation_stackLoad_fast_refined
#print axioms removalCostSimulation_stackStore_fast_refined
#print axioms removalCostSimulation_atomic_refined
end InitECandidate.Runtime.StackToLab
