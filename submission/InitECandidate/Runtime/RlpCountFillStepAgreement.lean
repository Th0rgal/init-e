import InitECandidate.Runtime.RlpListCountStepConsumed
import InitECandidate.Runtime.RlpSlicesStepConsumed
import InitECandidate.Runtime.RlpUncheckedItemTotalInputEqual
import InitECandidate.Runtime.RlpInputSuffixReads
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Counting and filling the same input at the same cursor advance equally. -/
theorem rlpCountFill_step_agreement {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer length offset count index : BitVec 64) (byte : UInt8)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedLength : checked.locals.lookup (ofString "len") = some (.val (.word length)))
    (checkedOffset : checked.locals.lookup (ofString "off") = some (.val (.word offset)))
    (checkedCount : checked.locals.lookup (ofString "count") = some (.val (.word count)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (uncheckedOffset : unchecked.locals.lookup (ofString "off") = some (.val (.word offset)))
    (uncheckedIndex : unchecked.locals.lookup (ofString "i") = some (.val (.word index)))
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
    checkedPost.locals.lookup (ofString "off") = uncheckedPost.locals.lookup (ofString "off") := by
  obtain ⟨size1,post1,run1,_,_,offset1,_⟩ := rlpListCount_step_consumed checked checkedPost pointer length offset count
    checkedPointer checkedLength checkedOffset checkedCount checkedCode checkedTicks checkedRun
  obtain ⟨size2,post2,run2,offset2,_⟩ := rlpSlices_step_consumed unchecked uncheckedPost pointer offset index
    uncheckedPointer uncheckedOffset uncheckedIndex uncheckedCode uncheckedRun
  let first := callEntryStateHOLFinite checked (rlpHeaderCallee (pointer + offset) (length - offset))
  let second := callEntryStateHOLFinite unchecked (HolFiniteMapExact.empty.update (ofString "p",.val (.word (pointer + offset))))
  have p1 : first.locals.lookup (ofString "p") = some (.val (.word (pointer + offset))) := by
    simp [first,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have n1 : first.locals.lookup (ofString "len") = some (.val (.word (length - offset))) := by
    simp [first,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have p2 : second.locals.lookup (ofString "p") = some (.val (.word (pointer + offset))) := by
    simp [second,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have nonzero : length - offset ≠ 0 := by
    intro zero
    have natural := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (show offset.toNat ≤ length.toNat by omega))
    rw [zero] at natural
    change 0 = length.toNat - offset.toNat at natural
    omega
  have suffix := rlpInput_suffix_reads checked unchecked pointer length offset (by omega) reads
  have equal := rlpUnchecked_item_total_input_equal first second post1 post2 (pointer + offset) (length - offset) byte
    (.val (.word size1)) (.val (.word size2)) p1 n1 p2 nonzero checkedCode uncheckedCode
    (by change 12 ≤ checked.clock - 1; omega) (by change 10 ≤ unchecked.clock - 1; omega)
    loaded suffix run1 run2
  have sizes : size1 = size2 := HolWordLab.word.inj (ValueHOL.val.inj equal)
  rw [offset1,offset2,sizes]

#print axioms rlpCountFill_step_agreement
end InitECandidate.Runtime
