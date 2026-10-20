import InitECandidate.Runtime.StackRemoveExecutedAtomic
import InitECandidate.Runtime.StackRemoveMemoryCompileCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem nativeCost_subRegister {F : Type} (gap destination input : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p) (subInst destination input) source = 1 + gap := by
  simp [subInst, stackExecutionCost, nativePriceWithGap, instLocalCost]

theorem nativeCost_rightShift {F : Type} (gap register count : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p) (StackRemove.rightShiftInst register count) source = 5 + gap := by
  simp [StackRemove.rightShiftInst, stackExecutionCost, nativePriceWithGap, instLocalCost]

theorem nativeCost_comp_opCurrHeap {F : Type} (gap pointer destination input : Nat) (op : HolBinop)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.opCurrHeap op destination input)) source = 1 + gap := by
  simp [StackRemove.comp, stackExecutionCost, nativePriceWithGap, instLocalCost]

theorem nativeCost_comp_stackGetSize {F : Type} (gap pointer register : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.stackGetSize register)) source ≤ 7 + 3 * gap := by
  rw [StackRemove.comp]
  have headBound (s : StackSemStateFiniteExact 64 LabToTarget.Config F) := nativeCost_seq_le gap
    (moveInst register pointer) (subInst register (pointer + 1)) (1 + gap) (1 + gap)
    (fun t => (nativeCost_move gap register pointer t).le)
    (fun t => (nativeCost_subRegister gap register (pointer + 1) t).le) s
  have bound := nativeCost_seq_le gap
    (.seq (moveInst register pointer) (subInst register (pointer + 1)))
    (StackRemove.rightShiftInst register (wordShiftAmount 64))
    ((1 + gap) + (1 + gap)) (5 + gap) headBound
    (fun t => (nativeCost_rightShift gap register (wordShiftAmount 64) t).le) source
  omega

theorem removalCostSimulation_opCurrHeap {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (op : HolBinop) (destination input : Nat) (localBound : 1 + gap ≤ sourcePrice (.opCurrHeap op destination input))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap jump bounds (.opCurrHeap op destination input) source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.Assembly.compCorrect (.opCurrHeap op destination input) source result post target pointer bounds jump premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · have sourceCost : stackExecutionCost (fun p _ => sourcePrice p) (.opCurrHeap op destination input) source = sourcePrice (.opCurrHeap op destination input) := by
      simp [stackExecutionCost]
    rw [sourceCost]
    exact ((nativeCost_comp_opCurrHeap gap pointer destination input op jump bounds _).le).trans localBound

theorem removalCostSimulation_stackGetSize {F : Type} (sourcePrice : HolProg 64 → Nat) (gap : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (register : Nat) (localBound : 7 + 3 * gap ≤ sourcePrice (.stackGetSize register))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    RemovalCostSimulation sourcePrice gap jump bounds (.stackGetSize register) source := by
  intro post target result pointer premises
  obtain ⟨clock, postTarget, targetRun, postRelation⟩ :=
    StackRemove.CompCorrect.Assembly.compCorrect (.stackGetSize register) source result post target pointer bounds jump premises
  refine ⟨clock, postTarget, targetRun, ?_, ?_⟩
  · cases result with
    | none => exact postRelation
    | some value => cases value <;> exact postRelation
  · have sourceCost : stackExecutionCost (fun p _ => sourcePrice p) (.stackGetSize register) source = sourcePrice (.stackGetSize register) := by
      simp [stackExecutionCost]
    rw [sourceCost]
    exact (nativeCost_comp_stackGetSize gap pointer register jump bounds _).trans localBound

#print axioms removalCostSimulation_opCurrHeap
#print axioms removalCostSimulation_stackGetSize
end InitECandidate.Runtime.StackToLab
