import InitECandidate.Runtime.StackRemoveExecutedLeaves
import InitECandidate.Runtime.StackRemoveExecutedExtras
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Executed source prices for the actual stack-removal configuration. Fast
memory offsets retain one instruction; large offsets and frames pay by size. -/
noncomputable def removalLocalPrice (gap : Nat) (bounds : BitVec 64 × BitVec 64) : HolProg 64 → Nat
  | .get _ _ | .set _ _ | .opCurrHeap _ _ _ => 1 + gap
  | .stackGetSize _ => 7 + 3 * gap
  | .stackLoad _ count =>
      if asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) then 1 + gap
      else (count / 255 + 3) * (1 + gap)
  | .stackStore _ count =>
      if asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) then 1 + gap
      else (count / 255 + 1) * (1 + gap) + (1 + gap) + (count / 255 + 1) * (1 + gap)
  | .stackFree count => ((count + 254) / 255) * (1 + gap)
  | .stackAlloc count => ((count + 254) / 255) * (7 + 3 * gap)
  | p => nativePriceWithGap gap p

theorem removalCostSimulation_stackLoad_fast {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register count : Nat)
    (fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true)
    (localBound : 1 + gap ≤ sourcePrice (.stackLoad register count))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap jump bounds (.stackLoad register count) source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.StackMemory.compCorrectStackLoad source result post target register count pointer bounds jump premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · have sourceCost : stackExecutionCost (fun p _ => sourcePrice p) (.stackLoad register count) source = sourcePrice (.stackLoad register count) := by
      simp [stackExecutionCost]
    rw [sourceCost]
    exact (nativeCost_comp_stackLoad_fast gap pointer register count jump bounds fast _).le.trans localBound

theorem removalCostSimulation_stackStore_fast {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register count : Nat)
    (fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true)
    (localBound : 1 + gap ≤ sourcePrice (.stackStore register count))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap jump bounds (.stackStore register count) source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.StackMemory.compCorrectStackStore source result post target register count pointer bounds jump premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · have sourceCost : stackExecutionCost (fun p _ => sourcePrice p) (.stackStore register count) source = sourcePrice (.stackStore register count) := by
      simp [stackExecutionCost]
    rw [sourceCost]
    exact (nativeCost_comp_stackStore_fast gap pointer register count jump bounds fast _).le.trans localBound

#print axioms removalCostSimulation_stackLoad_fast
#print axioms removalCostSimulation_stackStore_fast
end InitECandidate.Runtime.StackToLab
