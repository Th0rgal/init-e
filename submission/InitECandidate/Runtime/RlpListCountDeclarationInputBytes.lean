import InitECandidate.Runtime.RlpListCountDeclarationBelow
import InitECandidate.Runtime.InputBytesBelowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpListCount_declaration_normal_input_bytes {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (supported : readOnlyMemory continuation = true)
    (arguments : List (ExpHOL 64)) (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "rlp_list_count") arguments continuation) = (none,post))
    (before : pointer.toNat + length.toNat ≤ frame.toNat) (offset : Nat) (inside : offset < length.toNat) :
    @panMemLoadByteHOL 64 _ post.memory post.memaddrs
      (fun a => Classical.propDecidable (post.memaddrs a)) post.be (pointer + BitVec.ofNat 64 offset) =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + BitVec.ofNat 64 offset) := by
  have metadata := evaluateHOLFiniteState_metadata state
    (.decCall name .one (ofString "rlp_list_count") arguments continuation)
  rw [run] at metadata
  dsimp only at metadata
  apply input_bytes_of_memory_below state post pointer length frame before
  · intro address below
    exact rlpListCount_declaration_normal_below state post name continuation supported arguments
      pointer length scratch frame ceiling inputLimit args noWrap lengthBound limitBound scratchGlobal
      frameGlobal code orderedFrame framePositive scratchBelow arena budget run address below
  · exact metadata.2.1
  · exact metadata.2.2.1
  · exact inside

#print axioms rlpListCount_declaration_normal_input_bytes
end InitECandidate.Runtime
