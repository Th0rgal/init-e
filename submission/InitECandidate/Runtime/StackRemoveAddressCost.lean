import InitECandidate.Runtime.StackNativeGapPrice
import Flapjack.Compiler.Backend.StackRemove.StackAddress
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- A stopped prefix can only reduce the work of a straight-line composition. -/
theorem nativeCost_seq_le {F : Type} (gap : Nat) (first second : HolProg 64) (a b : Nat)
    (firstBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => nativePriceWithGap gap p) first s ≤ a)
    (secondBound : ∀ s : StackSemStateFiniteExact 64 LabToTarget.Config F,
      stackExecutionCost (fun p _ => nativePriceWithGap gap p) second s ≤ b)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p) (.seq first second) source ≤ a + b := by
  rw [stackExecutionCost_seq]
  simp only [show nativePriceWithGap gap (.seq first second) = 0 from rfl, Nat.zero_add]
  rcases StackSemEvaluate.evaluate (first, source) with ⟨result, middle⟩
  cases result with
  | none => exact Nat.add_le_add (firstBound source) (secondBound middle)
  | some _ => simpa only [Nat.add_zero] using (firstBound source).trans (Nat.le_add_right a b)

theorem nativeCost_address_add {F : Type} (gap register : Nat) (value : BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (.inst (.arith (.binop .add register register (.imm value)))) source = 1 + gap := by
  simp [stackExecutionCost, nativePriceWithGap, instLocalCost]

theorem nativeCost_address_sub {F : Type} (gap register : Nat) (value : BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (.inst (.arith (.binop .sub register register (.imm value)))) source = 1 + gap := by
  simp [stackExecutionCost, nativePriceWithGap, instLocalCost]

/-- Large offsets pay for each actually generated 255-word adjustment. -/
theorem nativeCost_upshift {F : Type} (gap register count : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.upshift register count) source ≤ (count / 255 + 1) * (1 + gap) := by
  rw [StackRemove.upshift]
  split
  · rw [nativeCost_address_add]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · rename_i large
    have recur := nativeCost_seq_le gap
      (.inst (.arith (.binop .add register register (.imm (StackRemove.wordOffset StackRemove.maxStackAlloc)))))
      (StackRemove.upshift register (count - StackRemove.maxStackAlloc)) (1 + gap)
      (((count - StackRemove.maxStackAlloc) / 255 + 1) * (1 + gap))
      (fun s => (nativeCost_address_add gap register (StackRemove.wordOffset StackRemove.maxStackAlloc) s).le)
      (fun s => nativeCost_upshift gap register (count - StackRemove.maxStackAlloc) s) source
    have divEq : (count - StackRemove.maxStackAlloc) / 255 + 1 = count / 255 := by
      simp only [StackRemove.maxStackAlloc] at *
      omega
    rw [divEq] at recur
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using recur
termination_by count
decreasing_by simp only [StackRemove.maxStackAlloc] at *; omega

/-- Restoring the address register has the same size-sensitive cost. -/
theorem nativeCost_downshift {F : Type} (gap register count : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.downshift register count) source ≤ (count / 255 + 1) * (1 + gap) := by
  rw [StackRemove.downshift]
  split
  · rw [nativeCost_address_sub]
    exact Nat.le_mul_of_pos_left _ (by omega)
  · rename_i large
    have recur := nativeCost_seq_le gap
      (.inst (.arith (.binop .sub register register (.imm (StackRemove.wordOffset StackRemove.maxStackAlloc)))))
      (StackRemove.downshift register (count - StackRemove.maxStackAlloc)) (1 + gap)
      (((count - StackRemove.maxStackAlloc) / 255 + 1) * (1 + gap))
      (fun s => (nativeCost_address_sub gap register (StackRemove.wordOffset StackRemove.maxStackAlloc) s).le)
      (fun s => nativeCost_downshift gap register (count - StackRemove.maxStackAlloc) s) source
    have divEq : (count - StackRemove.maxStackAlloc) / 255 + 1 = count / 255 := by
      simp only [StackRemove.maxStackAlloc] at *
      omega
    rw [divEq] at recur
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using recur
termination_by count
decreasing_by simp only [StackRemove.maxStackAlloc] at *; omega

#print axioms nativeCost_seq_le
#print axioms nativeCost_upshift
#print axioms nativeCost_downshift
end InitECandidate.Runtime.StackToLab
