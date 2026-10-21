import InitECandidate.Runtime.StackRefinedNativePrice
import InitECandidate.Runtime.StackRemovalLocalPrice
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Incremental refined pre-removal prices. Direct instructions and fast
memory operations use the padding-exclusive price. Complex frame operations
retain their existing proved conservative prices until separately tightened. -/
noncomputable def refinedRemovalLocalPrice (gap : Nat) (bounds : BitVec 64 × BitVec 64) : HolProg 64 → Nat
  | .get _ _ | .set _ _ | .opCurrHeap _ _ _ => 1 + (gap-1)
  | .stackLoad register count =>
      if asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) then 1+(gap-1)
      else removalLocalPrice gap bounds (.stackLoad register count)
  | .stackStore register count =>
      if asmOffsetOkExact 0 bounds (StackRemove.wordOffset count) then 1+(gap-1)
      else removalLocalPrice gap bounds (.stackStore register count)
  | .inst instruction => refinedNativePriceWithGap gap (.inst instruction)
  | .tick => refinedNativePriceWithGap gap .tick
  | p => removalLocalPrice gap bounds p

#print axioms refinedRemovalLocalPrice
end InitECandidate.Runtime.StackToLab
