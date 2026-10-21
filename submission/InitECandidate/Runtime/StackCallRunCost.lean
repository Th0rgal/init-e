import InitECandidate.Runtime.StackCallPriceCaps
import InitECandidate.Runtime.WordStackCallDestCost
import InitECandidate.Runtime.WordStackCallSetupCost
import Flapjack.Compiler.Backend.WordToStack.NativeReturn
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

variable {price : HolProg 64 → Nat} [caps : ConservativeRemovalPrice price]

/-- A proved prefix bound composes with the suffix at its actual poststate.
This preserves the state needed by the recursive compiler simulation. -/
theorem stackCost_seq_run {F : Type} (first second : HolProg 64)
    (source middle : StackSemStateFiniteExact 64 LabToTarget.Config F) (budget : Nat)
    (run : StackSemEvaluate.evaluate (first, source) = (none, middle))
    (bound : stackExecutionCost (fun p _ => price p) first source ≤ budget) :
    stackExecutionCost (fun p _ => price p)
      (.seq first second) source ≤ budget +
      stackExecutionCost (fun p _ => price p) second middle := by
  rw [stackExecutionCost_seq]
  simp only [show price (.seq first second) = 0 from ConservativeRemovalPrice.freeSeq _ _,
    Nat.zero_add, run]
  exact Nat.add_le_add_right bound _

/-- A tail call follows only its actual code lookup, without any multiplier
for code size or call depth. The callee state is exactly decClock source. -/
theorem stackCost_tail_call_found {F : Type} (dest : Sum Nat Nat) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (clock : source.clock ≠ 0)
    (found : StackSemControl.findCode dest source.regs source.code = some body) :
    stackExecutionCost (fun p _ => price p)
      (.call none dest none) source ≤ 2 +
      stackExecutionCost (fun p _ => price p)
        body (StackSemStateOps.decClock source) := by
  rw [stackExecutionCost]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, clock, found]
  have localBound : price (.call none dest none) ≤ 2 := by
    exact (caps.le _).trans (by cases dest <;> simp [removalLocalPrice, nativePriceWithGap, callJumpWork])
  exact Nat.add_le_add_right localBound _

/-- Clock exhaustion stops at the tail call and does not price a callee. -/
theorem stackCost_tail_call_zero {F : Type} (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) (clock : source.clock = 0) :
    stackExecutionCost (fun p _ => price p)
      (.call none dest none) source ≤ 2 := by
  rw [stackExecutionCost]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, clock]
  exact (caps.le _).trans (by cases dest <;> simp [removalLocalPrice, nativePriceWithGap, callJumpWork])

/-- Frame release composes at the real post-release state. -/
theorem stackCost_seqStackFree_run {F : Type} (count : Nat) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (small : count ≤ 92) (useStack : source.useStack = true)
    (fits : source.stackSpace + count ≤ source.stack.length) :
    stackExecutionCost (fun p _ => price p)
      (WordToStack.Native.seqStackFreeNative count body) source ≤ 7 +
      stackExecutionCost (fun p _ => price p)
        body {source with stackSpace := source.stackSpace + count} := by
  unfold WordToStack.Native.seqStackFreeNative
  split
  · rename_i zero
    simp only [zero, Nat.add_zero]
    exact Nat.le_add_left _ _
  · apply stackCost_seq_run (.stackFree count) body source _ 7
    · rw [StackSemEvaluate.evaluate_stackFree]
      simp only [useStack, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Nat.not_lt.mpr fits]
    · simpa only [stackExecutionCost] using ConservativeRemovalPrice.free count small

/-- Successful callee frame allocation pays 25 before its actual body state. -/
theorem stackCost_alloc_run {F : Type} (count : Nat) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (small : count ≤ 92) (useStack : source.useStack = true)
    (fits : count ≤ source.stackSpace) :
    stackExecutionCost (fun p _ => price p)
      (.seq (.stackAlloc count) body) source ≤ 25 +
      stackExecutionCost (fun p _ => price p)
        body {source with stackSpace := source.stackSpace - count} := by
  apply stackCost_seq_run (.stackAlloc count) body source _ 25
  · rw [StackSemEvaluate.evaluate_stackAlloc]
    simp only [useStack, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      Nat.not_lt.mpr fits]
  · simpa only [stackExecutionCost] using ConservativeRemovalPrice.alloc count small

#print axioms stackCost_seqStackFree_run
#print axioms stackCost_alloc_run

#print axioms stackCost_seq_run
#print axioms stackCost_tail_call_found
#print axioms stackCost_tail_call_zero
end InitECandidate.Runtime.StackToLab
