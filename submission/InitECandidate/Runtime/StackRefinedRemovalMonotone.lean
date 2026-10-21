import InitECandidate.Runtime.StackRefinedRemovalPrice
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Refined instruction/spill charges never invalidate a conservative fragment
bound. This permits incremental tightening of complex frame operations. -/
theorem refinedRemovalLocalPrice_le (gap : Nat) (bounds : BitVec 64 × BitVec 64) (p : HolProg 64) :
    refinedRemovalLocalPrice gap bounds p ≤ removalLocalPrice gap bounds p := by
  cases p <;> try (dsimp only [refinedRemovalLocalPrice]; exact Nat.le_refl _)
  case inst instruction => exact refinedNativePriceWithGap_le gap (.inst instruction)
  case tick => exact refinedNativePriceWithGap_le gap .tick
  case get register name => simp only [refinedRemovalLocalPrice, removalLocalPrice]; omega
  case set name register => simp only [refinedRemovalLocalPrice, removalLocalPrice]; omega
  case opCurrHeap operation destination input => simp only [refinedRemovalLocalPrice, removalLocalPrice]; omega
  case stackLoad register count =>
    simp only [refinedRemovalLocalPrice]
    split
    · simp only [removalLocalPrice, *, ↓reduceIte]; omega
    · exact Nat.le_refl _
  case stackStore register count =>
    simp only [refinedRemovalLocalPrice]
    split
    · simp only [removalLocalPrice, *, ↓reduceIte]; omega
    · exact Nat.le_refl _

#print axioms refinedRemovalLocalPrice_le
end InitECandidate.Runtime.StackToLab
