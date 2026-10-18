import InitECandidate.Runtime.AccessListSlotSlicesBound
import InitECandidate.Runtime.AccessListKeysAllocationProgress
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_slot_slices_progress {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (sliceLocal : state.locals.lookup (ofString "sl") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (budget : accessSlotSlicesCost length.toNat ≤ state.clock)
    (outerIndex : BitVec 64)
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (run : evaluateHOLFiniteState state accessSlotSlices = (none,final)) :
    final.locals.lookup (ofString "i") = some (.val (.word (outerIndex + 1))) ∧
      final.locals.lookup (ofString "lst") = state.locals.lookup (ofString "lst") ∧
      final.locals.lookup (ofString "recs") = state.locals.lookup (ofString "recs") := by
  let arguments : List (ExpHOL 64) := [.rfield 0 (.var .local (ofString "sl")),.rfield 1 (.var .local (ofString "sl"))]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,sliceLocal]
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ entry.clock := by
    change length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ state.clock - 1
    dsimp [accessSlotSlicesCost] at budget
    omega
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_access_slot_slices] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "slots") (ofString "rlp_list_to_slices") (.comb [.one,.one]) (.comb [.one,.one]) arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) accessKeysAllocation callee args lookup run
  rw [bodyRun] at bounded
  obtain ⟨count,shape,countBound,slices,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩ :=
    rlpSlices_body_returned_runtime_contract entry bodyPost pointer length scratch frame array ceiling inputLimit
      atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      heap arrayBound (by omega) heapArena entryBudget inputBeforeFrame inputBeforeArray value bodyRun
  subst value
  let resumed := setVarHOLFinite (ofString "slots") (.rStruct [.val (.word array),.val (.word count)]) {bodyPost with locals := state.locals}
  have listLocal : resumed.locals.lookup (ofString "slots") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have resumedSlices : RlpSliceInputPrefix resumed array pointer length count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := slices slot inside
    exact ⟨p,n,RlpSliceInputEntry.after_frame bodyPost resumed array slot p n pointer length item rfl rfl rfl⟩
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [bodyRun] at metadata
  have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
    intro address lower upper
    change bodyPost.memaddrs address
    rw [metadata.2.1]
    exact arena address lower upper
  have product : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have covers := allocationEnd_covers array (count * 16) (by rw [product]; exact interval)
  have factor := Nat.mul_le_mul_right (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92651) countBound
  have tailBudget : count.toNat * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92651) + 2 ≤ resumed.clock := by
    change count.toNat * (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92651) + 2 ≤ bodyPost.clock
    have cost := bounded.1
    change state.clock - 1 ≤ bodyPost.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3) at cost
    exact access_slot_slices_tail_budget length.toNat count.toNat state.clock bodyPost.clock countBound budget cost
  have resumedIndex : resumed.locals.lookup (ofString "i") = some (.val (.word outerIndex)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "slots" ≠ ofString "i" by decide] using binding
  have tail := access_keys_allocation_progress resumed output array count (allocationEnd array (count * 16)) pointer length scratch frame ceiling inputLimit
    listLocal resumedSlices scratchPost framePost (metadata.1.trans code) resumedArena lengthBound limitBound orderedFrame framePositive
    scratchBelow (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right 16 countBound) _) arrayBeforeFrame)
    (by rw [product] at covers; exact covers.1) aligned heapPost endpoint
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 32 (Nat.le_trans countBound lengthBound)) countLimit) tailBudget outerIndex resumedIndex tailRun
  rw [restored]
  refine ⟨?_,?_,?_⟩
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "slots",state.locals.lookup (ofString "slots"))).lookup (ofString "i") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact tail.1
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "slots",state.locals.lookup (ofString "slots"))).lookup (ofString "lst") = _
    rw [restore_other_local _ _ _ _ (by decide),tail.2.1]
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "slots" ≠ ofString "lst" by decide]
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "slots",state.locals.lookup (ofString "slots"))).lookup (ofString "recs") = _
    rw [restore_other_local _ _ _ _ (by decide),tail.2.2]
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "slots" ≠ ofString "recs" by decide]

#print axioms access_slot_slices_progress
end InitECandidate.Runtime
