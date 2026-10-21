import InitECandidate.Runtime.StackRemovalExecutedCorrect
import InitECandidate.Runtime.StackRemovalReachableCorrect
import InitECandidate.Runtime.StackRefinedRemovalLeafSimulation
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Closed local obligations for padding-exclusive instruction prices. -/
def refinedRemovalPriceCaps {F : Type} (gap : Nat) (bounds : BitVec 64 × BitVec 64) :
    RemovalPriceCaps (F := F) (refinedRemovalLocalPrice gap bounds) (refinedNativePriceWithGap gap) bounds where
  leaf := fun p source supported leaf => refinedRemovalCostSimulation_leaf gap bounds p source supported leaf
  freeSeq := fun _ _ => rfl
  branch := fun _ _ _ _ _ _ _ => Nat.le_refl _
  loopNode := fun _ _ => Nat.le_refl _
  tail := fun _ _ => Nat.le_refl _
  raw := fun _ => Nat.le_refl _
  returning := fun _ _ _ _ _ _ _ _ => Nat.le_refl _

/-- Actual evaluator transfer using the refined table throughout the run. -/
theorem refinedStackRemoval_cost_correct {F : Type} (gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : removalSupported p = true) (global : RemovalCodeSupported source.code)
    (oracle : EmptyInstallOracle source) :
    RemovalCostSimulationFor (refinedRemovalLocalPrice gap bounds) (refinedNativePriceWithGap gap) false bounds p source :=
  stackRemoval_cost_correctWithPrice _ _ bounds (refinedRemovalPriceCaps gap bounds) p source supported global oracle

/-- The same transfer permits installed code excluded by direct-call closure. -/
theorem refinedStackRemoval_cost_correct_reachable {F : Type} (forbidden gap : Nat) (bounds : BitVec 64 × BitVec 64)
    (p : HolProg 64) (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (supported : removalSupported p = true) (closed : directCallsAvoid forbidden p = true)
    (global : AvoidingRemovalCode forbidden source.code) (oracle : EmptyInstallOracle source) :
    RemovalCostSimulationFor (refinedRemovalLocalPrice gap bounds) (refinedNativePriceWithGap gap) false bounds p source :=
  stackRemoval_cost_correct_reachableWithPrice forbidden _ _ bounds
    (refinedRemovalPriceCaps gap bounds) p source supported closed global oracle

#print axioms refinedRemovalPriceCaps
#print axioms refinedStackRemoval_cost_correct
#print axioms refinedStackRemoval_cost_correct_reachable
end InitECandidate.Runtime.StackToLab
