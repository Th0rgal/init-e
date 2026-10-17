import InitECandidate.Runtime.ByteStoreChainFrame
import InitECandidate.Runtime.MemcpyByte8Progress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual unrolled byte-copy step preserves any word outside its eight
aligned destination cells, including failed source reads or stores. -/
theorem evaluate_memcpy_byte8_memory_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index watched : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (separate : ∀ offset : Nat, offset < 8 → watched ≠ panByteAlignHOL (destination + index + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState state memcpyByte8Body).2.memory watched = state.memory watched := by
  apply evaluate_byteStoreChain_frame (bindings := state.locals) (state := state) (locals := rfl)
  apply ByteStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 0 (by decide)⟩
    simp [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]
  apply ByteStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 1 (by decide)⟩
    simp [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]
  apply ByteStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 2 (by decide)⟩
    simp [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]
  apply ByteStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 3 (by decide)⟩
    simp [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]
  apply ByteStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 4 (by decide)⟩
    simp [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]
  apply ByteStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 5 (by decide)⟩
    simp [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]
  apply ByteStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 6 (by decide)⟩
    simp [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]
  apply ByteStoreChainFrame.store
  · intro current locals
    refine ⟨_,?_,separate 7 (by decide)⟩
    simp [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,evalHOLExact,evalListHOLExact,locals,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
      BitVec.add_assoc]
  exact ByteStoreChainFrame.tail _ rfl

#print axioms evaluate_memcpy_byte8_memory_frame
end InitECandidate.Runtime
