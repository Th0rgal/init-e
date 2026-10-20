import InitECandidate.Runtime.StackRemoveMemoryCompileCost
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Frame release costs one adjustment per 255 words; releasing zero is free. -/
theorem nativeCost_stackFree {F : Type} (gap pointer count : Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.stackFree pointer count) source ≤ ((count + 254) / 255) * (1 + gap) := by
  rw [StackRemove.stackFree]
  split
  · rename_i zero
    subst count
    simp [stackExecutionCost, nativePriceWithGap]
  · rename_i nonzero
    split
    · simp only [StackRemove.singleStackFree]
      rw [nativeCost_address_add]
      exact Nat.le_mul_of_pos_left _ (by omega)
    · rename_i large
      have bound := nativeCost_seq_le gap
        (StackRemove.singleStackFree pointer StackRemove.maxStackAlloc)
        (StackRemove.stackFree pointer (count - StackRemove.maxStackAlloc)) (1 + gap)
        (((count - StackRemove.maxStackAlloc + 254) / 255) * (1 + gap))
        (fun s => (nativeCost_address_add gap pointer _ s).le)
        (fun s => nativeCost_stackFree gap pointer (count - StackRemove.maxStackAlloc) s) source
      have divEq : (count + 254) / 255 = (count - StackRemove.maxStackAlloc + 254) / 255 + 1 := by
        simp only [StackRemove.maxStackAlloc] at *
        omega
      rw [divEq, Nat.add_mul, Nat.one_mul]
      simpa only [Nat.add_comm] using bound
termination_by count
decreasing_by simp only [StackRemove.maxStackAlloc] at *; omega

/-- Actual compiler output for a frame release retains the size-sensitive bound. -/
theorem nativeCost_comp_stackFree {F : Type} (gap pointer count : Nat)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.stackFree count)) source ≤
      ((count + 254) / 255) * (1 + gap) := by
  simpa only [StackRemove.comp] using nativeCost_stackFree gap pointer count source

/-- Store access is one native instruction, including the special current-heap register. -/
theorem nativeCost_comp_get {F : Type} (gap pointer register : Nat) (name : StoreName)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.get register name)) source = 1 + gap := by
  rw [StackRemove.comp]
  split
  · exact nativeCost_move gap register (pointer + 2) source
  · exact nativeCost_memory gap register .load _ source

theorem nativeCost_comp_set {F : Type} (gap pointer register : Nat) (name : StoreName)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => nativePriceWithGap gap p)
      (StackRemove.comp jump bounds pointer (.set name register)) source = 1 + gap := by
  rw [StackRemove.comp]
  split
  · exact nativeCost_move gap (pointer + 2) register source
  · exact nativeCost_memory gap register .store _ source

#print axioms nativeCost_stackFree
#print axioms nativeCost_comp_stackFree
#print axioms nativeCost_comp_get
#print axioms nativeCost_comp_set
end InitECandidate.Runtime.StackToLab
