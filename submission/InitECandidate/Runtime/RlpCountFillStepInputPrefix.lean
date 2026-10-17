import InitECandidate.Runtime.RlpCountFillStepInputEntry
import InitECandidate.Runtime.RlpSliceInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpCountFill_step_input_prefix {F : Type}
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
    (sliceCount : BitVec 64) (indexInside : index.toNat < sliceCount.toNat)
    (arrayFits : array.toNat + sliceCount.toNat * 16 ≤ 2^64)
    (filledPrefix : RlpSliceInputPrefix unchecked array pointer length index.toNat)
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
    RlpSliceInputPrefix uncheckedPost array pointer length (index + 1).toNat := by
  obtain ⟨consumed,entry⟩ := rlpCountFill_step_input_entry checked unchecked checkedPost uncheckedPost
    pointer length offset count index byte checkedPointer checkedLength checkedOffset checkedCount
    uncheckedPointer uncheckedOffset uncheckedIndex array arrayLocal domain0 domain8 noWrap inside
    checkedCode uncheckedCode checkedTicks uncheckedTicks loaded reads checkedRun uncheckedRun
  exact rlpSlices_step_extends_input_prefix unchecked uncheckedPost array index pointer offset
    arrayLocal uncheckedIndex uncheckedPointer uncheckedOffset domain0 domain8 sliceCount pointer length indexInside
    arrayFits filledPrefix ⟨pointer + offset,consumed,entry⟩ uncheckedCode uncheckedTicks uncheckedRun

#print axioms rlpCountFill_step_input_prefix
end InitECandidate.Runtime
