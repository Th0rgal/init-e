import InitECandidate.Runtime.StackStraightLineCost
import Flapjack.Compiler.Backend.StackRemove.StackAddress
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove

/-- The actual immediate-address expansion size, measured in 255-slot chunks. -/
def addressChunks (slots : Nat) : Nat := slots / 255 + 1

theorem upshift_fragment {width : Nat} [NeZero width] (register slots : Nat) :
    stackStraightLine (upshift (width := width) register slots) = true ∧
    stackLeaves (upshift (width := width) register slots) ≤ addressChunks slots := by
  rw [upshift]
  split
  · simp [stackStraightLine, stackLeaves, addressChunks]
  · have smaller := upshift_fragment (width := width) register (slots - maxStackAlloc)
    constructor
    · simpa only [stackStraightLine, Bool.true_and] using smaller.1
    · simp only [stackLeaves]
      simp only [addressChunks, maxStackAlloc] at *
      omega
termination_by slots
  decreasing_by simp only [maxStackAlloc] at *; omega

theorem downshift_fragment {width : Nat} [NeZero width] (register slots : Nat) :
    stackStraightLine (downshift (width := width) register slots) = true ∧
    stackLeaves (downshift (width := width) register slots) ≤ addressChunks slots := by
  rw [downshift]
  split
  · simp [stackStraightLine, stackLeaves, addressChunks]
  · have smaller := downshift_fragment (width := width) register (slots - maxStackAlloc)
    constructor
    · simpa only [stackStraightLine, Bool.true_and] using smaller.1
    · simp only [stackLeaves]
      simp only [addressChunks, maxStackAlloc] at *
      omega
termination_by slots
  decreasing_by simp only [maxStackAlloc] at *; omega

theorem stack_store_address_fragment {width : Nat} [NeZero width]
    (address register slots : Nat) :
    stackStraightLine (stackStore (width := width) address register slots) = true ∧
    stackLeaves (stackStore (width := width) address register slots) ≤
      2 * addressChunks slots + 1 := by
  have up := upshift_fragment (width := width) address slots
  have down := downshift_fragment (width := width) address slots
  constructor
  · simp only [stackStore, stackStraightLine, up.1, down.1, Bool.true_and]
  · simp only [stackStore, stackLeaves]
    omega

theorem stack_load_address_fragment {width : Nat} [NeZero width]
    (register slots : Nat) :
    stackStraightLine (stackLoad (width := width) register slots) = true ∧
    stackLeaves (stackLoad (width := width) register slots) ≤ addressChunks slots + 1 := by
  have up := upshift_fragment (width := width) register slots
  constructor
  · simp only [stackLoad, stackStraightLine, up.1, Bool.and_true]
  · simp only [stackLoad, stackLeaves]
    omega

#print axioms stack_store_address_fragment
#print axioms stack_load_address_fragment
end InitECandidate.Runtime.FineCost
