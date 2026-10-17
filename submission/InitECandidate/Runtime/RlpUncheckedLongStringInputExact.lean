import InitECandidate.Runtime.RlpHeaderLongStringFullReader
import InitECandidate.Runtime.RlpUncheckedLongReader
import InitECandidate.Runtime.RlpUncheckedLongDispatchValue
import InitECandidate.Runtime.RlpReadLengthBodyRangeAgreement
import InitECandidate.Runtime.RlpHeaderLongStringFullHeaderFits
import InitECandidate.Runtime.RlpReaderInputWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A checked long-string read bounds the unchecked branch's exact size when
the two source states supply the same byte reads, even at different clocks. -/
theorem rlpUnchecked_long_string_input_exact {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (uncheckedHeader : unchecked.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (lower : 183 < byte.toNat) (upper : byte.toNat ≤ 191) (nonzero : total ≠ 0)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : 11 ≤ checked.clock) (uncheckedTicks : 10 ≤ unchecked.clock)
    (loaded : @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
      (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be pointer = some byte)
    (reads : ∀ offset : Nat, offset < total.toNat → @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be (pointer + BitVec.ofNat 64 offset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be (pointer + BitVec.ofNat 64 offset))
    (checkedRun : evaluateHOLFiniteState checked (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpUncheckedAfterByte = (some (.returned uncheckedValue),uncheckedPost)) :
    ∃ headerSize payloadSize kind : BitVec 64,
      checkedValue = .rStruct [.val (.word headerSize),.val (.word payloadSize),.val (.word kind)] ∧
      uncheckedValue = .val (.word (headerSize + payloadSize)) := by
  have fits := rlpHeader_long_string_full_header_fits checked checkedPost pointer total byte checkedValue
    checkedPointer checkedTotal nonzero lower upper loaded checkedCode ticks checkedRun
  have readerReads := rlpReader_input_window checked unchecked pointer total ((BitVec.ofNat 64 byte.toNat) - 183) fits reads
  have low : 183 < (BitVec.ofNat 64 byte.toNat).toNat := by change 183 < byte.toNat % 2^64; omega
  have high : (BitVec.ofNat 64 byte.toNat).toNat ≤ 191 := by change byte.toNat % 2^64 ≤ 191; omega
  rw [evaluate_rlpUnchecked_long_string_after_load unchecked pointer (BitVec.ofNat 64 byte.toNat) uncheckedPointer uncheckedHeader low high uncheckedCode uncheckedTicks] at uncheckedRun
  obtain ⟨payload,readerPost1,readerRun1,shape,_,positive,bounded⟩ := rlpHeader_long_string_full_return_reader checked checkedPost pointer
    total byte checkedValue checkedPointer checkedTotal nonzero lower upper loaded checkedCode ticks checkedRun
  obtain ⟨decoded,readerPost2,readerRun2,returned⟩ := rlpUnchecked_long_string_returned_reader unchecked uncheckedPost pointer (BitVec.ofNat 64 byte.toNat)
    uncheckedPointer uncheckedHeader uncheckedCode uncheckedValue uncheckedRun
  let first := callEntryStateHOLFinite (setVarHOLFinite (ofString "ll") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 183))) (setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) checked)) (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 183))
  let second := callEntryStateHOLFinite (setVarHOLFinite (ofString "ll") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 183))) unchecked)
    (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 183))
  have registers : ∀ state : PanSemStateFiniteExact 64 F,
      (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 183))).locals.lookup (ofString "p") = some (.val (.word (pointer + 1))) ∧
      (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 183))).locals.lookup (ofString "n") = some (.val (.word ((BitVec.ofNat 64 byte.toNat) - 183))) := by
    intro state
    simp [callEntryStateHOLFinite,rlpReadLengthCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "n" ≠ ofString "p" by decide]
  have firstRegisters := registers (setVarHOLFinite (ofString "ll") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 183))) (setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) checked))
  have secondRegisters := registers (setVarHOLFinite (ofString "ll") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 183))) unchecked)
  have equal := rlpReadLength_body_returned_range_agreement first second readerPost1 readerPost2 (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 183)
    (.val (.word payload)) (.val (.word decoded)) firstRegisters.1 firstRegisters.2 secondRegisters.1 secondRegisters.2
    checkedCode uncheckedCode readerReads readerRun1 readerRun2
  have decodedEq : payload = decoded := HolWordLab.word.inj (ValueHOL.val.inj equal)
  subst decoded
  refine ⟨1 + ((BitVec.ofNat 64 byte.toNat) - 183),payload,0,shape,?_⟩
  simpa only [BitVec.add_assoc] using returned

#print axioms rlpUnchecked_long_string_input_exact
end InitECandidate.Runtime
