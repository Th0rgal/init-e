import InitECandidate.Runtime.StackRefinedRemovalPrice
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Optimized

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang
open InitECandidate.Runtime.StackToLab

/-- The local operations introduced by the actual raw-tail-call optimizer.
The recursive callee body is deliberately excluded: its execution must be
related separately by the whole-pass induction. -/
noncomputable def optimizedTailLocalCost (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) : Nat :=
  let price := refinedRemovalLocalPrice 6 bounds
  if allocated = released then price (.rawCall dest)
  else if allocated < released then
    price (.stackFree (released - allocated)) + price (.rawCall dest)
  else price .tick + price (.stackAlloc (allocated - released)) + price (.rawCall dest)

/-- Nonzero releases fund even the extra tick in the growing-frame case.
This is a local compiler-price inequality, not an assumed bound on the
optimized execution. Both frame bounds cover the actual guest's 92 slots. -/
theorem optimizedTailLocalCost_le (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) (positive : 0 < released)
    (releaseBound : released ≤ 255) (allocationBound : allocated ≤ 255) :
    optimizedTailLocalCost bounds released allocated dest ≤
      refinedRemovalLocalPrice 6 bounds (.stackFree released) +
      refinedRemovalLocalPrice 6 bounds (.call none (.inl dest) none) +
      refinedRemovalLocalPrice 6 bounds (.stackAlloc allocated) := by
  have releasedChunks : (released + 254) / 255 = 1 := by omega
  have allocatedChunks : (allocated + 254) / 255 ≤ 1 := by omega
  have freeChunks : (released - allocated + 254) / 255 ≤ 1 := by omega
  have allocChunks : (allocated - released + 254) / 255 ≤ 1 := by omega
  simp only [optimizedTailLocalCost, refinedRemovalLocalPrice,
    refinedNativePriceWithGap, removalLocalPrice, nativePriceWithGap,
    callJumpWork, instLocalCost, releasedChunks]
  split_ifs <;> omega

#print axioms optimizedTailLocalCost_le
end InitECandidate.Runtime.StackRawCall
