import InitECandidate.Runtime.WordStoreChainFrame
import InitECandidate.Runtime.LoadOneWord
import InitECandidate.Runtime.MemcpyWordProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_memcpy_word8_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (separate : ∀ offset : Nat, offset < 8 → watched ≠ destination + index + BitVec.ofNat 64 offset) :
    (evaluateHOLFiniteState state memcpyWord8Body).2.memory watched = state.memory watched := by
  apply evaluate_wordStoreChain_frame (bindings := state.locals) (state := state) (locals := rfl)
  apply WordStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 0 (by decide)⟩
    simp [memcpyAddress,
      evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  · intro current parsed evaluated
    exact eval_load_one_word current _ parsed evaluated
  exact WordStoreChainFrame.tail _ rfl

#print axioms evaluate_memcpy_word8_memory_frame
end InitECandidate.Runtime
