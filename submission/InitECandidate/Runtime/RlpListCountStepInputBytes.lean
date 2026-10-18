import InitECandidate.Runtime.RlpListCountStepBelow
import InitECandidate.Runtime.InputBytesSeparated
import InitECandidate.Runtime.RlpListCountStepAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpListCount_normal_step_input_bytes {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length offset scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (offsetBound : offset.toNat ≤ length.toNat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (2 * length.toNat + 1) * 15 + 18 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpListCountStep = (none,post))
    (before : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat)) (byteOffset : Nat) (inside : byteOffset < length.toNat) :
    @panMemLoadByteHOL 64 _ post.memory post.memaddrs
      (fun a => Classical.propDecidable (post.memaddrs a)) post.be (pointer + BitVec.ofNat 64 byteOffset) =
    @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun a => Classical.propDecidable (state.memaddrs a)) state.be (pointer + BitVec.ofNat 64 byteOffset) := by
  have metadata := evaluateHOLFiniteState_metadata state rlpListCountStep
  rw [run] at metadata
  dsimp only at metadata
  apply input_bytes_of_memory_separated state post pointer length frame ceiling before noWrap
  · intro address below
    exact rlpListCount_normal_step_below state post pointer length offset scratch frame ceiling inputLimit
      pointerLocal lengthLocal offsetLocal offsetBound noWrap lengthBound limitBound scratchGlobal frameGlobal
      code orderedFrame framePositive scratchBelow arena budget run address below
  · intro address above
    exact rlpListCount_normal_step_above state post pointer length offset scratch frame ceiling inputLimit
      pointerLocal lengthLocal offsetLocal offsetBound noWrap lengthBound limitBound scratchGlobal frameGlobal
      code orderedFrame framePositive scratchBelow arena budget run address above
  · exact metadata.2.1
  · exact metadata.2.2.1
  · exact inside

#print axioms rlpListCount_normal_step_input_bytes
end InitECandidate.Runtime
