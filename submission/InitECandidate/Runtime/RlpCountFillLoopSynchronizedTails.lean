import InitECandidate.Runtime.RlpCountFillLoopNormalTails
import InitECandidate.Runtime.RlpListCountLoopGuardAgreement
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpCountFill_loop_synchronized_tails {F : Type}
    (checked unchecked checkedPostFinal uncheckedPostFinal : PanSemStateFiniteExact 64 F)
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
    (sliceCount : BitVec 64)
    (arrayFits : array.toNat + sliceCount.toNat * 16 ≤ 2^64)
    (filledPrefix : RlpSliceInputPrefix unchecked array pointer length index.toNat)
    (noWrap : pointer.toNat + length.toNat < 2^64)
    (inside : offset.toNat < length.toNat)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (uncheckedTicks : 12 ≤ unchecked.clock)
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
    (countBound : count.toNat ≤ offset.toNat)
    (counterMatch : count = index)
    (checkedBudget : (length.toNat - offset.toNat) * ((2 * length.toNat + 1) * 15 + 19) ≤ checked.clock)
    (finalCount : checkedPostFinal.locals.lookup (ofString "count") = some (.val (.word sliceCount)))
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputAligned : pointer.toNat % 8 = 0)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (uncheckedCount : unchecked.locals.lookup (ofString "count") = some (.val (.word sliceCount)))
    (checkedRun : evaluateHOLFiniteState checked rlpListCountLoop = (none,checkedPostFinal))
    (uncheckedRun : evaluateHOLFiniteState unchecked rlpSlicesLoop = (none,uncheckedPostFinal)) :
    ∃ checkedPost uncheckedPost : PanSemStateFiniteExact 64 F,
    evaluateHOLFiniteState checkedPost rlpListCountLoop = (none,checkedPostFinal) ∧
    evaluateHOLFiniteState uncheckedPost rlpSlicesLoop = (none,uncheckedPostFinal) ∧
    checkedPost.locals.lookup (ofString "count") = some (.val (.word (count + 1))) ∧
    uncheckedPost.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
    RlpSliceInputPrefix uncheckedPost array pointer length (index + 1).toNat ∧
    ∃ consumed : BitVec 64,
      checkedPost.locals.lookup (ofString "off") = some (.val (.word (offset + consumed))) ∧
      uncheckedPost.locals.lookup (ofString "off") = some (.val (.word (offset + consumed))) ∧
      0 < consumed.toNat ∧ offset.toNat + consumed.toNat ≤ length.toNat ∧
      (offset + consumed).toNat = offset.toNat + consumed.toNat ∧
      length.toNat - (offset + consumed).toNat < length.toNat - offset.toNat ∧
      ∀ byteOffset : Nat, byteOffset < length.toNat →
        @panMemLoadByteHOL 64 _ checkedPost.memory checkedPost.memaddrs (fun a => Classical.propDecidable (checkedPost.memaddrs a)) checkedPost.be (pointer + BitVec.ofNat 64 byteOffset) =
        @panMemLoadByteHOL 64 _ uncheckedPost.memory uncheckedPost.memaddrs (fun a => Classical.propDecidable (uncheckedPost.memaddrs a)) uncheckedPost.be (pointer + BitVec.ofNat 64 byteOffset) := by
  let valid : RlpListCountLoopWitness checked pointer length scratch frame ceiling :=
    ⟨offset,count,checkedPointer,checkedLength,checkedOffset,checkedCount,countBound,
      by omega,scratchGlobal,frameGlobal,checkedCode,arena⟩
  have indexInside : index.toNat < sliceCount.toNat := by
    rw [← counterMatch]
    exact (rlpListCount_loop_guard_matches_final_count checked checkedPostFinal pointer length scratch frame ceiling inputLimit
      valid noWrap lengthBound limitBound orderedFrame framePositive scratchBelow checkedBudget sliceCount finalCount checkedRun).mp inside
  have iterationBudget : (2 * length.toNat + 1) * 15 + 19 ≤ checked.clock := by
    exact Nat.le_trans (Nat.le_mul_of_pos_left _ (by omega : 0 < length.toNat - offset.toNat)) checkedBudget
  exact rlpCountFill_loop_normal_tails checked unchecked checkedPostFinal uncheckedPostFinal
    pointer length offset count index checkedPointer checkedLength checkedOffset checkedCount
    uncheckedPointer uncheckedOffset uncheckedIndex array arrayLocal domain0 domain8 sliceCount indexInside
    arrayFits filledPrefix noWrap inside checkedCode uncheckedCode (by omega) uncheckedTicks reads
    scratch frame ceiling inputLimit lengthBound limitBound scratchGlobal frameGlobal orderedFrame framePositive
    scratchBelow arena iterationBudget inputBeforeFrame inputAligned inputBeforeArray uncheckedCount checkedRun uncheckedRun

#print axioms rlpCountFill_loop_synchronized_tails
end InitECandidate.Runtime
