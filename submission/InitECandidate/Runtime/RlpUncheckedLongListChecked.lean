import InitECandidate.Runtime.RlpHeaderLongListReadReader
import InitECandidate.Runtime.RlpUncheckedLongReader
import InitECandidate.Runtime.RlpReadLengthBodyAgreement
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A checked long-list read bounds the unchecked branch's exact size when
the two source states supply the same byte reads, even at different clocks. -/
theorem rlpUnchecked_long_list_checked_bound {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedLength : checked.locals.lookup (ofString "ll") = some (.val (.word (header - 247))))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (uncheckedHeader : unchecked.locals.lookup (ofString "b") = some (.val (.word header)))
    (headerFits : 1 + (header - 247).toNat ≤ total.toNat)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : (header - 247).toNat + 2 ≤ checked.clock)
    (reads : ∀ address, @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be address =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be address)
    (checkedRun : evaluateHOLFiniteState checked rlpHeaderLongListRead = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpUncheckedLongList = (some (.returned uncheckedValue),uncheckedPost)) :
    ∃ consumed : BitVec 64, uncheckedValue = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat := by
  obtain ⟨payload,readerPost1,readerRun1,_,_,positive,bounded⟩ := rlpHeader_long_list_read_return_reader checked checkedPost pointer
    (header - 247) total checkedValue checkedPointer checkedLength checkedTotal headerFits checkedCode ticks checkedRun
  obtain ⟨decoded,readerPost2,readerRun2,returned⟩ := rlpUnchecked_long_list_returned_reader unchecked uncheckedPost pointer header
    uncheckedPointer uncheckedHeader uncheckedCode uncheckedValue uncheckedRun
  let first := callEntryStateHOLFinite checked (rlpReadLengthCallee (pointer + 1) (header - 247))
  let second := callEntryStateHOLFinite (setVarHOLFinite (ofString "ll2") (.val (.word (header - 247))) unchecked)
    (rlpReadLengthCallee (pointer + 1) (header - 247))
  have registers : ∀ state : PanSemStateFiniteExact 64 F,
      (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) (header - 247))).locals.lookup (ofString "p") = some (.val (.word (pointer + 1))) ∧
      (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) (header - 247))).locals.lookup (ofString "n") = some (.val (.word (header - 247))) := by
    intro state
    simp [callEntryStateHOLFinite,rlpReadLengthCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "n" ≠ ofString "p" by decide]
  have firstRegisters := registers checked
  have secondRegisters := registers (setVarHOLFinite (ofString "ll2") (.val (.word (header - 247))) unchecked)
  have equal := rlpReadLength_body_returned_agreement first second readerPost1 readerPost2 (pointer + 1) (header - 247)
    (.val (.word payload)) (.val (.word decoded)) firstRegisters.1 firstRegisters.2 secondRegisters.1 secondRegisters.2
    checkedCode uncheckedCode reads readerRun1 readerRun2
  have decodedEq : payload = decoded := HolWordLab.word.inj (ValueHOL.val.inj equal)
  subst decoded
  exact ⟨1 + ((header - 247) + payload),returned,positive,bounded⟩

#print axioms rlpUnchecked_long_list_checked_bound
end InitECandidate.Runtime
