import InitECandidate.Runtime.StackRemoveMemoryCost
import Flapjack.Compiler.Backend.StackRemove.Comp
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

theorem nativeCost_move {F : Type} (gap destination register : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p) (moveInst destination register) source = 1 + gap := by
  simp [moveInst, moveHOL, stackExecutionCost, nativePriceWithGap, instLocalCost]

/-- Actual stack-load compilation, including the destination-register copy
required by the large-offset path. -/
theorem nativeCost_comp_stackLoad {F : Type} (gap pointer register count : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.stackLoad register count)) source ≤
      (count / 255 + 3) * (1 + gap) := by
  rw [StackRemove.comp]
  split
  · rw [nativeCost_memory]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · have bound := nativeCost_seq_le gap (moveInst register pointer) (StackRemove.stackLoad register count)
      (1 + gap) ((count / 255 + 2) * (1 + gap))
      (fun s => (nativeCost_move gap register pointer s).le)
      (fun s => nativeCost_stackLoad gap register count s) source
    simpa only [Nat.add_mul, Nat.one_mul, Nat.succ_mul, Nat.add_assoc, Nat.add_comm] using bound

/-- Actual stack-store compilation: fast offsets use one memory instruction;
large offsets additionally restore the stack pointer after storing. -/
theorem nativeCost_comp_stackStore {F : Type} (gap pointer register count : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.stackStore register count)) source ≤
      (count / 255 + 1) * (1 + gap) + (1 + gap) + (count / 255 + 1) * (1 + gap) := by
  rw [StackRemove.comp]
  split
  · rw [nativeCost_memory]
    omega
  · exact nativeCost_stackStore gap pointer register count source

/-- Immediate-offset loads retain their exact one-instruction local price. -/
theorem nativeCost_comp_stackLoad_fast {F : Type} (gap pointer register count : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.stackLoad register count)) source = 1 + gap := by
  simp only [StackRemove.comp, fast, ↓reduceIte]
  exact nativeCost_memory gap register .load _ source

/-- Immediate-offset stores likewise avoid charging address-adjustment code. -/
theorem nativeCost_comp_stackStore_fast {F : Type} (gap pointer register count : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (fast : asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) = true)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.stackStore register count)) source = 1 + gap := by
  simp only [StackRemove.comp, fast, ↓reduceIte]
  exact nativeCost_memory gap register .store _ source

#print axioms nativeCost_comp_stackLoad_fast
#print axioms nativeCost_comp_stackStore_fast
#print axioms nativeCost_comp_stackLoad
#print axioms nativeCost_comp_stackStore
end InitECandidate.Runtime.StackToLab
