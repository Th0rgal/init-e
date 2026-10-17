import InitECandidate.Runtime.RlpHeaderLongListFullReader
import InitECandidate.Runtime.RlpUncheckedLongReader
import InitECandidate.Runtime.RlpUncheckedLongDispatchValue
import InitECandidate.Runtime.RlpReadLengthBodyAgreement
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A checked long-list read bounds the unchecked branch's exact size when
the two source states supply the same byte reads, even at different clocks. -/
theorem rlpUnchecked_long_list_full_checked_bound {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (uncheckedHeader : unchecked.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))))
    (lower : 247 < byte.toNat) (upper : byte.toNat ≤ 255) (nonzero : total ≠ 0)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : 11 ≤ checked.clock) (uncheckedTicks : 10 ≤ unchecked.clock)
    (loaded : @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
      (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be pointer = some byte)
    (reads : ∀ address, @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be address =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be address)
    (checkedRun : evaluateHOLFiniteState checked (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpUncheckedAfterByte = (some (.returned uncheckedValue),uncheckedPost)) :
    ∃ consumed : BitVec 64, uncheckedValue = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat := by
  have low : 247 < (BitVec.ofNat 64 byte.toNat).toNat := by change 247 < byte.toNat % 2^64; omega
  have high : (BitVec.ofNat 64 byte.toNat).toNat ≤ 255 := by change byte.toNat % 2^64 ≤ 255; omega
  rw [evaluate_rlpUnchecked_long_list_after_load unchecked pointer (BitVec.ofNat 64 byte.toNat) uncheckedPointer uncheckedHeader low high uncheckedCode uncheckedTicks] at uncheckedRun
  obtain ⟨payload,readerPost1,readerRun1,_,_,positive,bounded⟩ := rlpHeader_long_list_full_return_reader checked checkedPost pointer
    total byte checkedValue checkedPointer checkedTotal nonzero lower upper loaded checkedCode ticks checkedRun
  obtain ⟨decoded,readerPost2,readerRun2,returned⟩ := rlpUnchecked_long_list_returned_reader unchecked uncheckedPost pointer (BitVec.ofNat 64 byte.toNat)
    uncheckedPointer uncheckedHeader uncheckedCode uncheckedValue uncheckedRun
  let first := callEntryStateHOLFinite (setVarHOLFinite (ofString "ll") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 247))) (setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) checked)) (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 247))
  let second := callEntryStateHOLFinite (setVarHOLFinite (ofString "ll2") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 247))) unchecked)
    (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 247))
  have registers : ∀ state : PanSemStateFiniteExact 64 F,
      (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 247))).locals.lookup (ofString "p") = some (.val (.word (pointer + 1))) ∧
      (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 247))).locals.lookup (ofString "n") = some (.val (.word ((BitVec.ofNat 64 byte.toNat) - 247))) := by
    intro state
    simp [callEntryStateHOLFinite,rlpReadLengthCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "n" ≠ ofString "p" by decide]
  have firstRegisters := registers (setVarHOLFinite (ofString "ll") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 247))) (setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) checked))
  have secondRegisters := registers (setVarHOLFinite (ofString "ll2") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 247))) unchecked)
  have equal := rlpReadLength_body_returned_agreement first second readerPost1 readerPost2 (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 247)
    (.val (.word payload)) (.val (.word decoded)) firstRegisters.1 firstRegisters.2 secondRegisters.1 secondRegisters.2
    checkedCode uncheckedCode reads readerRun1 readerRun2
  have decodedEq : payload = decoded := HolWordLab.word.inj (ValueHOL.val.inj equal)
  subst decoded
  exact ⟨1 + (((BitVec.ofNat 64 byte.toNat) - 247) + payload),returned,positive,bounded⟩

#print axioms rlpUnchecked_long_list_full_checked_bound
end InitECandidate.Runtime
