import InitECandidate.Runtime.KeyToNibblesGeneralPair
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every actual nibble store pair preserves every existing nibble range,
including overlapping ranges and modular output addresses. -/
theorem evaluate_keyNibble_offset_pair_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (offset : Nat) (byte : UInt8) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1)))) :
    ∃ post, evaluateHOLFiniteState state (keyNibbleOffsetPair name offset) = (none,post) ∧
      (∀ nibs length, TrieNibbleRange state nibs length → TrieNibbleRange post nibs length) ∧
      post.locals = state.locals ∧ post.clock = state.clock ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨cell,cellRead⟩ : ∃ cell : BitVec 64,
      state.memory (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))) = .word cell := by
    cases state.memory (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))) with
    | word cell => exact ⟨cell,rfl⟩
  let middle := sourceWriteByte state (out + (2 * index + BitVec.ofNat 64 offset))
    ((BitVec.ofNat 64 byte.toNat) >>> (4 : Nat)) cell
  have addresses := eval_keyNibble_offset_output state out index offset outLocal indexLocal
  have values := eval_keyNibble_values state name byte byteLocal
  have first := evaluate_source_storeByte state _ _ _ _ cell addresses.1 values.1 firstDomain cellRead
  obtain ⟨nextCell,nextRead⟩ : ∃ cell : BitVec 64,
      middle.memory (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1))) = .word cell := by
    cases middle.memory (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1))) with
    | word cell => exact ⟨cell,rfl⟩
  have nextAddresses := eval_keyNibble_offset_output middle out index offset outLocal indexLocal
  have nextValues := eval_keyNibble_values middle name byte byteLocal
  have second := evaluate_source_storeByte middle _ _ _ _ nextCell
    nextAddresses.2 nextValues.2 secondDomain nextRead
  refine ⟨sourceWriteByte middle (out + ((2 * index + BitVec.ofNat 64 offset) + 1))
    ((BitVec.ofNat 64 byte.toNat) &&& 15) nextCell,?_,?_,rfl,rfl,rfl,rfl⟩
  · unfold keyNibbleOffsetPair
    rw [evaluateHOLFiniteState_seq_line780,first]
    exact second
  · intro nibs length valid
    have firstValid : TrieNibbleRange middle nibs length :=
      valid.after_small_byte _ _ cell (keyNibble_high_small byte) firstDomain cellRead
    exact firstValid.after_small_byte _ _ nextCell
      (keyNibble_low_small (BitVec.ofNat 64 byte.toNat)) secondDomain nextRead

/-- The original right-associated pair of writes preserves prior ranges
before entering any continuation. -/
theorem evaluate_keyNibble_prefix_then_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (offset : Nat) (byte : UInt8) (continuation : ProgHOL 64) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1)))) :
    ∃ middle, evaluateHOLFiniteState state (keyNibbleStoresThen name offset continuation) =
      evaluateHOLFiniteState middle continuation ∧
      (∀ nibs length, TrieNibbleRange state nibs length → TrieNibbleRange middle nibs length) ∧
      middle.locals = state.locals ∧ middle.clock = state.clock ∧
      middle.memaddrs = state.memaddrs ∧ middle.be = state.be := by
  obtain ⟨middle,run,preserve,locals,clock,domain,endian⟩ :=
    evaluate_keyNibble_offset_pair_preserves state name offset byte out index outLocal indexLocal byteLocal
      firstDomain secondDomain
  refine ⟨middle,?_,preserve,locals,clock,domain,endian⟩
  rw [evaluate_keyNibble_stores_then,evaluateHOLFiniteState_seq_line780,run]

#print axioms evaluate_keyNibble_prefix_then_preserves
#print axioms evaluate_keyNibble_offset_pair_preserves
end InitECandidate.Runtime
