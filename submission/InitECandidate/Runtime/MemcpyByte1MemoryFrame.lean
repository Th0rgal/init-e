import InitECandidate.Runtime.ByteStoreChainFrame
import InitECandidate.Runtime.MemcpyByteStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_memcpy_byte1_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (separate : watched ≠ panByteAlignHOL (destination + index)) :
    (evaluateHOLFiniteState state memcpyByte1Body).2.memory watched = state.memory watched := by
  apply evaluate_byteStoreChain_frame (bindings := state.locals) (state := state) (locals := rfl)
  apply ByteStoreChainFrame.store
  · intro current locals
    exact ⟨destination + index,eval_memcpyAddress current (ofString "dst") destination index
      (by rw [locals]; exact dstLocal) (by rw [locals]; exact indexLocal),separate⟩
  exact ByteStoreChainFrame.tail _ rfl

#print axioms evaluate_memcpy_byte1_memory_frame
end InitECandidate.Runtime
