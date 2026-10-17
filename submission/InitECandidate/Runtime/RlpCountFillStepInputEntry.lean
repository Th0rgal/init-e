import InitECandidate.Runtime.RlpCountFillStepConsumedProgress
import InitECandidate.Runtime.RlpSlicesStepEntryCursor
import InitECandidate.Runtime.RlpSliceInputSpan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpCountFill_step_input_entry {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer length offset count index : BitVec 64) (byte : UInt8)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedLength : checked.locals.lookup (ofString "len") = some (.val (.word length)))
    (checkedOffset : checked.locals.lookup (ofString "off") = some (.val (.word offset)))
    (checkedCount : checked.locals.lookup (ofString "count") = some (.val (.word count)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (uncheckedOffset : unchecked.locals.lookup (ofString "off") = some (.val (.word offset)))
    (uncheckedIndex : unchecked.locals.lookup (ofString "i") = some (.val (.word index)))
    (array : BitVec 64)
    (arrayLocal : unchecked.locals.lookup (ofString "arr") = some (.val (.word array)))
    (domain0 : unchecked.memaddrs (array + index * 16#64))
    (domain8 : unchecked.memaddrs (array + index * 16#64 + 8#64))
    (noWrap : pointer.toNat + length.toNat < 2^64)
    (inside : offset.toNat < length.toNat)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (checkedTicks : 13 ≤ checked.clock) (uncheckedTicks : 11 ≤ unchecked.clock)
    (loaded : @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
      (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + offset) = some byte)
    (reads : ∀ byteOffset : Nat, byteOffset < length.toNat →
      @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + BitVec.ofNat 64 byteOffset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs (fun a => Classical.propDecidable (unchecked.memaddrs a)) unchecked.be (pointer + BitVec.ofNat 64 byteOffset))
    (checkedRun : evaluateHOLFiniteState checked rlpListCountStep = (none,checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpSlicesStep = (none,uncheckedPost)) :
    ∃ consumed : BitVec 64, RlpSliceInputEntry uncheckedPost array index (pointer + offset) consumed pointer length := by
  obtain ⟨consumed,_,cursor,positive,fits,_⟩ := rlpCountFill_step_consumed_progress checked unchecked checkedPost uncheckedPost
    pointer length offset count index byte checkedPointer checkedLength checkedOffset checkedCount
    uncheckedPointer uncheckedOffset uncheckedIndex inside checkedCode uncheckedCode checkedTicks uncheckedTicks loaded reads checkedRun uncheckedRun
  obtain ⟨stored,entry,storedCursor⟩ := rlpSlices_step_entry_cursor unchecked uncheckedPost array index pointer offset
    arrayLocal uncheckedIndex uncheckedPointer uncheckedOffset domain0 domain8 uncheckedCode uncheckedTicks uncheckedRun
  have words : offset + stored = offset + consumed := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (storedCursor.symm.trans cursor)))
  have equal : stored = consumed := (BitVec.add_right_inj offset).mp words
  subst stored
  exact ⟨consumed,rlpSliceInputEntry_of_cursor uncheckedPost array index pointer length offset consumed entry noWrap fits⟩

#print axioms rlpCountFill_step_input_entry
end InitECandidate.Runtime
