import InitECandidate.Runtime.RlpSlicesUpdatesByteFrame
import InitECandidate.Runtime.RlpSlicesInputSeparation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_updates_input_bytes {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset total : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (totalLocal : state.locals.lookup (ofString "total") = some (.val (.word total)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (run : evaluateHOLFiniteState state rlpSlicesUpdates = (none,post))
    (input length count : BitVec 64)
    (inputAligned : input.toNat % 8 = 0)
    (inputBefore : input.toNat + length.toNat ≤ array.toNat)
    (inside : index.toNat < count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (byteOffset : Nat) (offsetInside : byteOffset < length.toNat) :
    @panMemLoadByteHOL 64 _ post.memory post.memaddrs
      (fun address => Classical.propDecidable (post.memaddrs address)) post.be (input + BitVec.ofNat 64 byteOffset) =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be (input + BitVec.ofNat 64 byteOffset) := by
  have separate := rlpSlices_input_cells_separate input length array index count inputAligned inputBefore inside fits byteOffset offsetInside
  exact rlpSlices_updates_byte_frame state post array index pointer offset total arrayLocal indexLocal pointerLocal offsetLocal totalLocal
    domain0 domain8 run (input + BitVec.ofNat 64 byteOffset) separate.1 separate.2

#print axioms rlpSlices_updates_input_bytes
end InitECandidate.Runtime
