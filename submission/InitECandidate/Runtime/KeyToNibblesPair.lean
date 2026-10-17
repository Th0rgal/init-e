import InitECandidate.Runtime.KeyToNibblesValues
import InitECandidate.Runtime.MemzeroSyntax
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keyNibblePair (name : MlS) : ProgHOL 64 :=
  .seq (.storeByte (keyNibbleOutputAddress 0) (.shift .lsr (.var .local name) (.const 4)))
    (.storeByte (keyNibbleOutputAddress 1) (.op .and [.var .local name,.const 15]))

theorem eval_keyNibble_output {F : Type} (state : PanSemStateFiniteExact 64 F)
    (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    (@evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (keyNibbleOutputAddress 0) =
      some (.val (.word (out + 2 * index)))) ∧
    (@evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (keyNibbleOutputAddress 1) =
      some (.val (.word (out + (2 * index + 1))))) := by
  constructor <;> simp [keyNibbleOutputAddress,evalHOLExact,evalListHOLExact,outLocal,indexLocal,
    wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]

/-- The actual pair of source writes extends the nibble prefix by two. The
second cell is read after the first write, so shared-word stores are covered. -/
theorem evaluate_keyNibble_pair {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (byte : UInt8) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (bounded : (2 * index).toNat < 63)
    (valid : TrieNibbleRange state out (2 * index))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + 2 * index)))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + 1)))) :
    ∃ post, evaluateHOLFiniteState state (keyNibblePair name) = (none,post) ∧
      TrieNibbleRange post out (2 * index + 1 + 1) ∧
      post.locals = state.locals ∧ post.clock = state.clock ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨cell,cellRead⟩ : ∃ cell : BitVec 64,
      state.memory (panByteAlignHOL (out + 2 * index)) = .word cell := by
    cases state.memory (panByteAlignHOL (out + 2 * index)) with
    | word cell => exact ⟨cell,rfl⟩
  let middle := sourceWriteByte state (out + 2 * index)
    ((BitVec.ofNat 64 byte.toNat) >>> (4 : Nat)) cell
  have addresses := eval_keyNibble_output state out index outLocal indexLocal
  have values := eval_keyNibble_values state name byte byteLocal
  have first := evaluate_source_storeByte state _ _ _ _ cell addresses.1 values.1 firstDomain cellRead
  have firstRange : TrieNibbleRange middle out (2 * index + 1) :=
    TrieNibbleRange.append_byte state out (2 * index) _ cell valid (by omega)
      (keyNibble_high_small byte) firstDomain cellRead
  obtain ⟨nextCell,nextRead⟩ : ∃ cell : BitVec 64,
      middle.memory (panByteAlignHOL (out + (2 * index + 1))) = .word cell := by
    cases middle.memory (panByteAlignHOL (out + (2 * index + 1))) with
    | word cell => exact ⟨cell,rfl⟩
  have nextAddresses := eval_keyNibble_output middle out index outLocal indexLocal
  have nextValues := eval_keyNibble_values middle name byte byteLocal
  have second := evaluate_source_storeByte middle _ _ _ _ nextCell
    nextAddresses.2 nextValues.2 secondDomain nextRead
  have nextBound : (2 * index + 1).toNat < 64 := by
    rw [BitVec.toNat_add]
    change ((2 * index).toNat + 1) % 18446744073709551616 < 64
    omega
  refine ⟨_,?_,TrieNibbleRange.append_byte middle out (2 * index + 1) _ nextCell
    firstRange nextBound (keyNibble_low_small (BitVec.ofNat 64 byte.toNat)) secondDomain nextRead,rfl,rfl,rfl,rfl⟩
  unfold keyNibblePair
  rw [evaluateHOLFiniteState_seq_line780,first]
  exact second

theorem evaluate_keyNibble_pair_advance {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (byte : UInt8) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (bounded : (2 * index).toNat < 63)
    (valid : TrieNibbleRange state out (2 * index))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + 2 * index)))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + 1)))) :
    ∃ post, evaluateHOLFiniteState state (.seq (keyNibblePair name) (memzeroAdvance 1)) = (none,post) ∧
      TrieNibbleRange post out (2 * (index + 1)) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.clock = state.clock := by
  obtain ⟨middle,run,range,locals,clock,domain,endian⟩ :=
    evaluate_keyNibble_pair state name byte out index outLocal indexLocal byteLocal
      bounded valid firstDomain secondDomain
  have indexNow : middle.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [locals]; exact indexLocal
  have advance := evaluate_memzero_advance middle index 1 indexNow
  have arithmetic : 2 * index + 1 + 1 = 2 * (index + 1) := by
    simp [BitVec.mul_add,BitVec.add_assoc]
  refine ⟨setVarHOLFinite (ofString "i") (.val (.word (index + 1))) middle,?_,?_,?_,clock⟩
  · rw [evaluateHOLFiniteState_seq_line780,run]
    exact advance
  · rw [← arithmetic]
    exact range.after_frame rfl rfl rfl
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms evaluate_keyNibble_pair_advance
#print axioms eval_keyNibble_output
#print axioms evaluate_keyNibble_pair
end InitECandidate.Runtime
