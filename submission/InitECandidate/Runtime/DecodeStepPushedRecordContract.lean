import InitECandidate.Runtime.DecodeStepBodyRecordMetadata
import InitECandidate.Runtime.DecodeStepReturnedProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem decode_step_body_pushed_record_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepBodyCost inputLimit ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (aligned : array.toNat%8=0) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) (record : BitVec 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_step) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    DecoderPushedTable post record pointer length pointer length ceiling ∧
      record = scratchAllocationEnd scratch 88 ∧ frame.toNat ≤ record.toNat ∧ record.toNat+88 ≤ scratch.toNat ∧
      ∀ offset : Nat, offset < 88 → post.memaddrs (record+BitVec.ofNat 64 offset) := by
  have table := decode_step_body_push_returned_table s post pointer length scratch frame array ceiling inputLimit atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget heap
    arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap record run
  have parseMono := decodeStepParseCost_mono length.toNat inputLimit lengthBound
  have pushCost : decodeStepListPushCost inputLimit ≤ decodeStepTwoCaseCost inputLimit := by
    unfold decodeStepListPushCost decodeStepTwoCaseCost; omega
  have pushBudget : decodeStepParseCost length.toNat +
      (decodeStepSlicesCost inputLimit+decodeStepListPushCost inputLimit) ≤ s.clock :=
    (Nat.add_le_add parseMono (Nat.add_le_add_left pushCost _)).trans budget
  have identity := decode_step_entry_push_returned_record s post pointer length scratch frame array record ceiling inputLimit
    atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
    arena pushBudget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray run
  obtain ⟨_,lower,upper⟩ := decode_step_entry_push_returned_progress s post pointer length scratch frame array record ceiling inputLimit
    atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
    arena pushBudget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray run
  rw [← identity] at lower upper
  have metadata := evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn__decode_step)
  rw [run] at metadata
  refine ⟨table,identity,lower,upper,?_⟩
  intro offset inside
  have offsetNat : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have addressNat : (record+BitVec.ofNat 64 offset).toNat = record.toNat+offset := by
    rw [BitVec.toNat_add,offsetNat]
    exact Nat.mod_eq_of_lt (by have limit := scratch.isLt; omega)
  rw [metadata.2.1]
  exact arena _ (by rw [addressNat]; omega) (by rw [addressNat]; omega)

#print axioms decode_step_body_pushed_record_contract
end InitECandidate.Runtime
