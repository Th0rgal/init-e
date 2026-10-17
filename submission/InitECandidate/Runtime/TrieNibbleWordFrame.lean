import InitECandidate.Runtime.TrieNibbleRangeGeneral
import InitECandidate.Runtime.FrameHalt
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- A word store outside the containing words of a path preserves all of
its nibble values, regardless of the stored metadata value. -/
theorem TrieNibbleRange.after_word_outside {F : Type} {state : PanSemStateFiniteExact 64 F}
    {nibs length : BitVec 64} (valid : TrieNibbleRange state nibs length)
    (address value : BitVec 64)
    (outside : ∀ offset : Nat, offset < length.toNat →
      panByteAlignHOL (nibs + BitVec.ofNat 64 offset) ≠ address) :
    TrieNibbleRange (sourceWriteWord state address value) nibs length := by
  intro offset inside byte loaded
  apply valid offset inside byte
  have different := outside offset inside
  change @panMemLoadByteHOL 64 _ (sourceWriteWord state address value).memory
    state.memaddrs (fun a => Classical.propDecidable (state.memaddrs a)) state.be
    (nibs + BitVec.ofNat 64 offset) = some byte at loaded
  simpa [panMemLoadByteHOL,sourceWriteWord,different] using loaded

#print axioms TrieNibbleRange.after_word_outside
end InitECandidate.Runtime
