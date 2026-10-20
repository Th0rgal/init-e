import InitECandidate.Runtime.StackRemoveExecutedSimulation
import InitECandidate.Runtime.StackRemoveAllocationCost
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StoreTransfers
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackMemory
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem removalCostSimulation_get {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register : Nat) (name : StoreName)
    (localBound : 1 + gap ≤ sourcePrice (.get register name))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap jump bounds (.get register name) source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.StoreTransfers.compCorrectGet source result post target pointer bounds jump register name premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · have sourceCost : stackExecutionCost (fun p _ => sourcePrice p) (.get register name) source = sourcePrice (.get register name) := by
      simp [stackExecutionCost]
    rw [sourceCost]
    exact ((nativeCost_comp_get gap pointer register name jump bounds _).le).trans localBound

theorem removalCostSimulation_set {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register : Nat) (name : StoreName)
    (localBound : 1 + gap ≤ sourcePrice (.set name register))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap jump bounds (.set name register) source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.StoreTransfers.compCorrectSet source result post target pointer bounds jump register name premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · have sourceCost : stackExecutionCost (fun p _ => sourcePrice p) (.set name register) source = sourcePrice (.set name register) := by
      simp [stackExecutionCost]
    rw [sourceCost]
    exact ((nativeCost_comp_set gap pointer register name jump bounds _).le).trans localBound

theorem removalCostSimulation_stackLoad {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register count : Nat)
    (localBound : (count / 255 + 3) * (1 + gap) ≤ sourcePrice (.stackLoad register count))
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
    exact (nativeCost_comp_stackLoad gap pointer register count jump bounds _).trans localBound

theorem removalCostSimulation_stackStore {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register count : Nat)
    (localBound : (count / 255 + 1) * (1 + gap) + (1 + gap) + (count / 255 + 1) * (1 + gap) ≤ sourcePrice (.stackStore register count))
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
    exact (nativeCost_comp_stackStore gap pointer register count jump bounds _).trans localBound

theorem removalCostSimulation_stackFree {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (count : Nat)
    (localBound : ((count + 254) / 255) * (1 + gap) ≤ sourcePrice (.stackFree count))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap jump bounds (.stackFree count) source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.StackSpace.compCorrectStackFree source result post target count pointer bounds jump premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · have sourceCost : stackExecutionCost (fun p _ => sourcePrice p) (.stackFree count) source = sourcePrice (.stackFree count) := by
      simp [stackExecutionCost]
    rw [sourceCost]
    exact (nativeCost_comp_stackFree gap pointer count jump bounds _).trans localBound

theorem removalCostSimulation_stackAlloc {F : Type} (sourcePrice : HolProg 64 → Nat) (gap count : Nat) (bounds : BitVec 64 × BitVec 64)
    (localBound : ((count + 254) / 255) * (7 + 3 * gap) ≤ sourcePrice (.stackAlloc count))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap false bounds (.stackAlloc count) source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.StackSpace.compCorrectStackAlloc source result post target count pointer bounds false premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · have sourceCost : stackExecutionCost (fun p _ => sourcePrice p) (.stackAlloc count) source = sourcePrice (.stackAlloc count) := by
      simp [stackExecutionCost]
    rw [sourceCost]
    exact (nativeCost_comp_stackAlloc gap pointer count bounds _).trans localBound

#print axioms removalCostSimulation_get
#print axioms removalCostSimulation_set
#print axioms removalCostSimulation_stackLoad
#print axioms removalCostSimulation_stackStore
#print axioms removalCostSimulation_stackFree
#print axioms removalCostSimulation_stackAlloc
end InitECandidate.Runtime.StackToLab
