import InitECandidate.Runtime.RlpListCountBodyBelow
import InitECandidate.Runtime.InputBytesBelowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpListCount_body_returned_input_bytes {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_list_count) = (some (.returned value),post))
    (before : pointer.toNat + length.toNat ≤ frame.toNat) (offset : Nat) (inside : offset < length.toNat) :
    @panMemLoadByteHOL 64 _ post.memory post.memaddrs
      (fun a => Classical.propDecidable (post.memaddrs a)) post.be (pointer + BitVec.ofNat 64 offset) =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + BitVec.ofNat 64 offset) := by
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_rlp_list_count)
  rw [run] at metadata
  dsimp only at metadata
  apply input_bytes_of_memory_below state post pointer length frame before
  · intro address below
    exact rlpListCount_body_returned_below state post pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
      framePositive scratchBelow arena budget value run address below
  · exact metadata.2.1
  · exact metadata.2.2.1
  · exact inside

#print axioms rlpListCount_body_returned_input_bytes
end InitECandidate.Runtime
