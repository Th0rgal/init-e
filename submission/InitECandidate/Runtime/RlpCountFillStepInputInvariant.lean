import InitECandidate.Runtime.RlpCountFillStepInputPrefix
import InitECandidate.Runtime.RlpCountFillStepConsumedProgress
import InitECandidate.Runtime.RlpListCountStepInputBytes
import InitECandidate.Runtime.RlpSlicesStepInputBytesUnaligned
import InitECandidate.Runtime.RlpListCountStepReadable
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpCountFill_step_retains_input_invariant {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer length offset count index : BitVec 64)
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
    (reads : ∀ byteOffset : Nat, byteOffset < length.toNat →
      @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs (fun a => Classical.propDecidable (checked.memaddrs a)) checked.be (pointer + BitVec.ofNat 64 byteOffset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs (fun a => Classical.propDecidable (unchecked.memaddrs a)) unchecked.be (pointer + BitVec.ofNat 64 byteOffset))
    (scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (lengthBound : length.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : checked.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : checked.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → checked.memaddrs address)
    (checkedBudget : (2 * length.toNat + 1) * 15 + 18 ≤ checked.clock)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (checkedRun : evaluateHOLFiniteState checked rlpListCountStep = (none,checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpSlicesStep = (none,uncheckedPost)) :
    RlpSliceInputPrefix uncheckedPost array pointer length (index + 1).toNat ∧
    ∃ consumed : BitVec 64,
      checkedPost.locals.lookup (ofString "off") = some (.val (.word (offset + consumed))) ∧
      uncheckedPost.locals.lookup (ofString "off") = some (.val (.word (offset + consumed))) ∧
      0 < consumed.toNat ∧ offset.toNat + consumed.toNat ≤ length.toNat ∧
      (offset + consumed).toNat = offset.toNat + consumed.toNat ∧
      ∀ byteOffset : Nat, byteOffset < length.toNat →
        @panMemLoadByteHOL 64 _ checkedPost.memory checkedPost.memaddrs (fun a => Classical.propDecidable (checkedPost.memaddrs a)) checkedPost.be (pointer + BitVec.ofNat 64 byteOffset) =
        @panMemLoadByteHOL 64 _ uncheckedPost.memory uncheckedPost.memaddrs (fun a => Classical.propDecidable (uncheckedPost.memaddrs a)) uncheckedPost.be (pointer + BitVec.ofNat 64 byteOffset) := by
  obtain ⟨byte,loaded⟩ := rlpListCount_normal_step_readable checked checkedPost pointer length offset count
    checkedPointer checkedLength checkedOffset checkedCount inside checkedCode checkedTicks checkedRun
  have filled := rlpCountFill_step_input_prefix checked unchecked checkedPost uncheckedPost
    pointer length offset count index byte checkedPointer checkedLength checkedOffset checkedCount
    uncheckedPointer uncheckedOffset uncheckedIndex array arrayLocal domain0 domain8 sliceCount indexInside
    arrayFits filledPrefix noWrap inside checkedCode uncheckedCode checkedTicks uncheckedTicks loaded reads checkedRun uncheckedRun
  obtain ⟨consumed,checkedOff,uncheckedOff,positive,fits,natural⟩ :=
    rlpCountFill_step_consumed_progress checked unchecked checkedPost uncheckedPost
      pointer length offset count index byte checkedPointer checkedLength checkedOffset checkedCount
      uncheckedPointer uncheckedOffset uncheckedIndex inside checkedCode uncheckedCode checkedTicks uncheckedTicks
      loaded reads checkedRun uncheckedRun
  refine ⟨filled,consumed,checkedOff,uncheckedOff,positive,fits,natural,?_⟩
  intro byteOffset byteInside
  have checkedBytes := rlpListCount_normal_step_input_bytes checked checkedPost pointer length offset scratch frame ceiling inputLimit
    checkedPointer checkedLength checkedOffset (by omega) noWrap lengthBound limitBound scratchGlobal frameGlobal
    checkedCode orderedFrame framePositive scratchBelow arena checkedBudget checkedRun inputBeforeFrame byteOffset byteInside
  have uncheckedBytes := rlpSlices_step_input_bytes_unaligned unchecked uncheckedPost array index pointer offset
    arrayLocal uncheckedIndex uncheckedPointer uncheckedOffset domain0 domain8 uncheckedCode uncheckedTicks uncheckedRun
    pointer length sliceCount inputBeforeArray indexInside arrayFits byteOffset byteInside
  exact checkedBytes.trans ((reads byteOffset byteInside).trans uncheckedBytes.symm)

#print axioms rlpCountFill_step_retains_input_invariant
end InitECandidate.Runtime
