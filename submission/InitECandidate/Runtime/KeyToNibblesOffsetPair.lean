import InitECandidate.Runtime.KeyToNibblesPair
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keyNibbleOffsetPair (name : MlS) (offset : Nat) : ProgHOL 64 :=
  .seq (.storeByte (keyNibbleOutputAddress offset) (.shift .lsr (.var .local name) (.const 4)))
    (.storeByte (keyNibbleOutputAddress (offset + 1)) (.op .and [.var .local name,.const 15]))

theorem eval_keyNibble_offset_output {F : Type} (state : PanSemStateFiniteExact 64 F)
    (out index : BitVec 64) (offset : Nat)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    (@evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (keyNibbleOutputAddress offset) =
      some (.val (.word (out + (2 * index + BitVec.ofNat 64 offset))))) ∧
    (@evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (keyNibbleOutputAddress (offset + 1)) =
      some (.val (.word (out + ((2 * index + BitVec.ofNat 64 offset) + 1))))) := by
  by_cases zero : offset = 0
  · subst offset
    simpa using eval_keyNibble_output state out index outLocal indexLocal
  · constructor <;> simp [keyNibbleOutputAddress,zero,evalHOLExact,evalListHOLExact,outLocal,indexLocal,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,BitVec.ofNat_add,BitVec.add_assoc]

/-- The actual pair of source writes extends the nibble prefix by two. The
second cell is read after the first write, so shared-word stores are covered. -/
theorem evaluate_keyNibble_offset_pair {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (offset : Nat) (byte : UInt8) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (bounded : ((2 * index + BitVec.ofNat 64 offset)).toNat < 63)
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
    TrieNibbleRange.append_byte state out ((2 * index + BitVec.ofNat 64 offset)) _ cell valid (by omega)
      (keyNibble_high_small byte) firstDomain cellRead
  obtain ⟨nextCell,nextRead⟩ : ∃ cell : BitVec 64,
      middle.memory (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1))) = .word cell := by
    cases middle.memory (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1))) with
    | word cell => exact ⟨cell,rfl⟩
  have nextAddresses := eval_keyNibble_offset_output middle out index offset outLocal indexLocal
  have nextValues := eval_keyNibble_values middle name byte byteLocal
  have second := evaluate_source_storeByte middle _ _ _ _ nextCell
    nextAddresses.2 nextValues.2 secondDomain nextRead
  have nextBound : ((2 * index + BitVec.ofNat 64 offset) + 1).toNat < 64 := by
    rw [BitVec.toNat_add]
    change (((2 * index + BitVec.ofNat 64 offset)).toNat + 1) % 18446744073709551616 < 64
    omega
  refine ⟨_,?_,TrieNibbleRange.append_byte middle out ((2 * index + BitVec.ofNat 64 offset) + 1) _ nextCell
    firstRange nextBound (keyNibble_low_small (BitVec.ofNat 64 byte.toNat)) secondDomain nextRead,rfl,rfl,rfl,rfl⟩
  unfold keyNibbleOffsetPair
  rw [evaluateHOLFiniteState_seq_line780,first]
  exact second

/-- Original right-associated stores followed by an arbitrary continuation. -/
def keyNibbleStoresThen (name : MlS) (offset : Nat) (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.storeByte (keyNibbleOutputAddress offset) (.shift .lsr (.var .local name) (.const 4)))
    (.seq (.storeByte (keyNibbleOutputAddress (offset + 1)) (.op .and [.var .local name,.const 15])) continuation)

theorem evaluate_keyNibble_stores_then {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (offset : Nat) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState state (keyNibbleStoresThen name offset continuation) =
      evaluateHOLFiniteState state (.seq (keyNibbleOffsetPair name offset) continuation) :=
  (evaluate_seq_assoc state _ _ continuation).symm

def keyNibbleByteThen (name : MlS) (byteOffset : Nat) (continuation : ProgHOL 64) : ProgHOL 64 :=
  .dec name .one (.loadByte (.op .add
    ([.var .local (ofString "key"),.var .local (ofString "i")] ++
      if byteOffset = 0 then [] else [.const (BitVec.ofNat 64 byteOffset)])))
    (keyNibbleStoresThen name (2 * byteOffset) continuation)

/-- All four loads and eight writes are exactly those of the frozen source. -/
theorem source_keyNibble_main_step : keyToNibblesMainStep =
    keyNibbleByteThen (ofString "b0") 0
      (keyNibbleByteThen (ofString "b1") 1
        (keyNibbleByteThen (ofString "b2") 2
          (keyNibbleByteThen (ofString "b3") 3 (memzeroAdvance 4)))) := by
  simp only [keyToNibblesMainStep,keyToNibblesMainLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_keyNibble_prefix_then {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (offset : Nat) (byte : UInt8) (continuation : ProgHOL 64) (out index : BitVec 64)
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (byteLocal : state.locals.lookup name = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (bounded : ((2 * index + BitVec.ofNat 64 offset)).toNat < 63)
    (valid : TrieNibbleRange state out ((2 * index + BitVec.ofNat 64 offset)))
    (firstDomain : state.memaddrs (panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset))))
    (secondDomain : state.memaddrs (panByteAlignHOL (out + ((2 * index + BitVec.ofNat 64 offset) + 1)))) :
    ∃ middle, evaluateHOLFiniteState state (keyNibbleStoresThen name offset continuation) =
      evaluateHOLFiniteState middle continuation ∧
      TrieNibbleRange middle out ((2 * index + BitVec.ofNat 64 offset) + 1 + 1) ∧
      middle.locals = state.locals ∧ middle.clock = state.clock ∧
      middle.memaddrs = state.memaddrs ∧ middle.be = state.be := by
  obtain ⟨middle,run,range,locals,clock,domain,endian⟩ :=
    evaluate_keyNibble_offset_pair state name offset byte out index outLocal indexLocal byteLocal
      bounded valid firstDomain secondDomain
  refine ⟨middle,?_,range,locals,clock,domain,endian⟩
  rw [evaluate_keyNibble_stores_then,evaluateHOLFiniteState_seq_line780,run]

#print axioms evaluate_keyNibble_prefix_then
#print axioms evaluate_keyNibble_stores_then
#print axioms source_keyNibble_main_step
#print axioms eval_keyNibble_offset_output
#print axioms evaluate_keyNibble_offset_pair
end InitECandidate.Runtime
