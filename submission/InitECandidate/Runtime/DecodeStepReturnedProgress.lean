import InitECandidate.Runtime.DecodeStepCompletedWorkspace
import InitECandidate.Runtime.DecodeStepScratchCapacity
import InitECandidate.Runtime.DecodeStepPushRecordIdentity
import InitECandidate.Runtime.DecodeStepReturnedTag
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem listPushCost_le_twoCase (n : Nat) : decodeStepListPushCost n ≤ decodeStepTwoCaseCost n := by
  unfold decodeStepListPushCost decodeStepTwoCaseCost
  omega

/-- The actual decoder never increases remaining stack capacity. Completed nodes
retain it; pending nodes strictly consume capacity and return the fresh record. -/
theorem decode_step_body_returned_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712) (flag record : BitVec 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn__decode_step) =
      (some (.returned (.rStruct [.val (.word flag),.val (.word record)])),post)) :
    (flag = 0 ∨ flag = 1) ∧
    decoderScratchCapacity frame post ≤ decoderScratchCapacity frame s ∧
    (flag = 0 → decoderScratchCapacity frame post = decoderScratchCapacity frame s) ∧
    (flag = 1 → decoderScratchCapacity frame post < decoderScratchCapacity frame s ∧
      record = scratchAllocationEnd scratch 88) := by
  have parseMono := decodeStepParseCost_mono length.toNat inputLimit lengthBound
  have parseBudget : decodeStepParseCost length.toNat ≤ s.clock :=
    parseMono.trans ((Nat.le_add_right _ _).trans budget)
  obtain ⟨tag,payload,tags,same⟩ := decode_step_entry_returned_tag s post pointer length scratch frame ceiling inputLimit
    atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena parseBudget _ run
  have tagEq : flag = tag := HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (ValueHOL.rStruct.inj same)).1)
  subst tag
  rcases tags with zero | one
  · subst flag
    have kept := decode_step_body_completed_workspace s post pointer length scratch frame array ceiling inputLimit
      atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena budget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap
      (.val (.word record)) run
    have capacity : decoderScratchCapacity frame post = decoderScratchCapacity frame s := by
      simp only [decoderScratchCapacity,kept.1,scratchGlobal]
    exact ⟨Or.inl rfl,capacity.le,fun _ => capacity,by simp⟩
  · subst flag
    have pushBudget : decodeStepParseCost length.toNat +
        (decodeStepSlicesCost inputLimit + decodeStepListPushCost inputLimit) ≤ s.clock :=
      (Nat.add_le_add parseMono (Nat.add_le_add_left (listPushCost_le_twoCase inputLimit) _)).trans budget
    have smaller := decode_step_entry_push_decreases_capacity s post pointer length scratch frame array record
      ceiling inputLimit atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
      framePositive scratchBelow arena pushBudget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray run
    have identity := decode_step_entry_push_returned_record s post pointer length scratch frame array record
      ceiling inputLimit atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
      framePositive scratchBelow arena pushBudget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray run
    exact ⟨Or.inr rfl,smaller.le,by simp,fun _ => ⟨smaller,identity⟩⟩

#print axioms decode_step_body_returned_progress
end InitECandidate.Runtime
