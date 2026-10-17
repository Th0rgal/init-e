import InitECandidate.Runtime.KeyToNibblesOffsetPair
import InitECandidate.Runtime.TrieNibbleRangeGeneral
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual pair of source writes extends the nibble prefix by two. The
second cell is read after the first write, so shared-word stores are covered. -/
theorem evaluate_keyNibble_offset_pair_no_wrap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (offset : Nat) (byte : UInt8) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (bounded : ((2 * index + BitVec.ofNat 64 offset)).toNat + 2 < 2^64)
    (valid : TrieNibbleRange state out ((2 * index + BitVec.ofNat 64 offset)))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1)))) :
    ∃ post, evaluateHOLFiniteState state (keyNibbleOffsetPair name offset) = (none,post) ∧
      TrieNibbleRange post out ((2 * index + BitVec.ofNat 64 offset) + 1 + 1) ∧
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
  have firstRange : TrieNibbleRange middle out ((2 * index + BitVec.ofNat 64 offset) + 1) :=
    TrieNibbleRange.append_byte_no_wrap state out ((2 * index + BitVec.ofNat 64 offset)) _ cell valid (by omega)
      (keyNibble_high_small byte) firstDomain cellRead
  obtain ⟨nextCell,nextRead⟩ : ∃ cell : BitVec 64,
      middle.memory (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1))) = .word cell := by
    cases middle.memory (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1))) with
    | word cell => exact ⟨cell,rfl⟩
  have nextAddresses := eval_keyNibble_offset_output middle out index offset outLocal indexLocal
  have nextValues := eval_keyNibble_values middle name byte byteLocal
  have second := evaluate_source_storeByte middle _ _ _ _ nextCell
    nextAddresses.2 nextValues.2 secondDomain nextRead
  have nextBound : ((2 * index + BitVec.ofNat 64 offset) + 1).toNat + 1 < 2^64 := by
    rw [BitVec.toNat_add]
    change (((2 * index + BitVec.ofNat 64 offset)).toNat + 1) % 18446744073709551616 + 1 < 2^64
    omega
  refine ⟨_,?_,TrieNibbleRange.append_byte_no_wrap middle out ((2 * index + BitVec.ofNat 64 offset) + 1) _ nextCell
    firstRange nextBound (keyNibble_low_small (BitVec.ofNat 64 byte.toNat)) secondDomain nextRead,rfl,rfl,rfl,rfl⟩
  unfold keyNibbleOffsetPair
  rw [evaluateHOLFiniteState_seq_line780,first]
  exact second

theorem evaluate_keyNibble_prefix_then_no_wrap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (offset : Nat) (byte : UInt8) (continuation : ProgHOL 64) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (bounded : ((2 * index + BitVec.ofNat 64 offset)).toNat + 2 < 2^64)
    (valid : TrieNibbleRange state out ((2 * index + BitVec.ofNat 64 offset)))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1)))) :
    ∃ middle, evaluateHOLFiniteState state (keyNibbleStoresThen name offset continuation) =
      evaluateHOLFiniteState middle continuation ∧
      TrieNibbleRange middle out ((2 * index + BitVec.ofNat 64 offset) + 1 + 1) ∧
      middle.locals = state.locals ∧ middle.clock = state.clock ∧
      middle.memaddrs = state.memaddrs ∧ middle.be = state.be := by
  obtain ⟨middle,run,range,locals,clock,domain,endian⟩ :=
    evaluate_keyNibble_offset_pair_no_wrap state name offset byte out index outLocal indexLocal byteLocal
      bounded valid firstDomain secondDomain
  refine ⟨middle,?_,range,locals,clock,domain,endian⟩
  rw [evaluate_keyNibble_stores_then,evaluateHOLFiniteState_seq_line780,run]

#print axioms evaluate_keyNibble_offset_pair_no_wrap
#print axioms evaluate_keyNibble_prefix_then_no_wrap
end InitECandidate.Runtime
