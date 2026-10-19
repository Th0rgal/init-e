import InitECandidate.Runtime.DecodeHeaderListEntryReach
import InitECandidate.Runtime.RlpSlicesBodyOuterRuntimeContract
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.RlpSliceInputPrefixBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

def decodeHeaderSlicesCost (limit : Nat) : Nat := limit * ((2 * limit + 1) * 15 + 19) + limit * 12 + 4

/-- The original header list-to-slices declaration builds the actual readable
field table and aligned heap endpoint, or terminates within its quadratic budget. -/
theorem decode_header_slices_entry_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer size consumed scratch frame array input inputLength : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top") =
      some (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word size),.val (.word consumed)]))
    (noWrap : pointer.toNat + size.toNat < 2^64) (lengthBound : size.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + size.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + size.toNat ≤ array.toNat)
    (starts : input.toNat ≤ pointer.toNat) (ends : pointer.toNat + size.toNat ≤ input.toNat + inputLength.toNat)
    (budget : decodeHeaderSlicesCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 2)
      (fun ready => ∃ count : BitVec 64,
        count.toNat ≤ inputLength.toNat ∧
        ready.locals = s.locals.update (ofString "lst",.rStruct [.val (.word array),.val (.word count)]) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
        ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
        (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧ (allocationEnd array (count * 16)).toNat % 8 = 0)
      (decodeHeaderSlicesCost inputLimit) (decodeHeaderAt 3) := by
  let callee := rlpHeaderCallee pointer size
  let entry := callEntryStateHOLFinite s callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word size)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 1 (.var .local (ofString "top")),.rfield 2 (.var .local (ofString "top"))] =
      some [.val (.word pointer),.val (.word size)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atTop]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer size (by decide)
    (by rw [code]; exact originalRuntimeCode_rlpSlices_lookup)
  have product := Nat.mul_le_mul lengthBound (by omega : (2 * size.toNat + 1) * 15 + 19 ≤ (2 * inputLimit + 1) * 15 + 19)
  have bodyBudget : size.toNat * ((2 * size.toNat + 1) * 15 + 19) + size.toNat * 12 + 3 ≤ entry.clock := by
    change _ ≤ s.clock - 1
    unfold decodeHeaderSlicesCost at budget
    omega
  have bounded := evaluate_rlpSlices_body_bounded entry pointer size scratch frame ceiling inputLimit p len noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena bodyBudget
  rw [source_decode_header_slices]
  unfold decodeHeaderSlicesCost
  rw [show inputLimit * ((2 * inputLimit + 1) * 15 + 19) + inputLimit * 12 + 4 = (inputLimit * ((2 * inputLimit + 1) * 15 + 19) + inputLimit * 12 + 3) + 1 by omega]
  apply bounded_decCall_reaches s _ _ _ _ _ _ _ _ callee (inputLimit * ((2 * inputLimit + 1) * 15 + 19) + inputLimit * 12 + 3) _ args lookup (by exact budget)
    ((show RunBounded entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
      (size.toNat * ((2 * size.toNat + 1) * 15 + 19) + size.toNat * 12 + 3) from bounded).weaken (by omega))
  intro value post returned _
  obtain ⟨count,valueEq,countBound,table,heapBinding,scratchBinding,frameBinding,_,extent,cap,al⟩ :=
    rlpSlices_body_returned_outer_runtime_contract entry post pointer size scratch frame array input inputLength ceiling inputLimit
      p len noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound
      countLimit heapArena bodyBudget inputBeforeFrame inputBeforeArray starts ends value returned
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [returned] at metadata
  let ready := setVarHOLFinite (ofString "lst") value {post with locals := s.locals}
  have readyTable : RlpSliceInputPrefix ready array input inputLength count.toNat :=
    table.after_memory_below post ready array count input inputLength (allocationEnd array (count * 16)) extent rfl (fun _ _ => rfl)
  refine ⟨count,countBound,?_,readyTable,heapBinding,scratchBinding,frameBinding,metadata.2.1,metadata.1,extent,cap,al⟩
  change s.locals.update (ofString "lst",value) = _
  rw [valueEq]

#print axioms decode_header_slices_entry_reaches
end InitECandidate.Runtime
