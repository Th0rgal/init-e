import InitECandidate.Runtime.RlpSlicesBodyOuterPrefix
import InitECandidate.Runtime.RlpSliceInputPrefixOuter
import InitECandidate.Runtime.AccessListSlotSlicesBound
import InitECandidate.Runtime.AccessListKeysAllocationIndependentOuterPrefix
import InitECandidate.Runtime.PanDecCallCheckedNormalExactScope
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_slot_slices_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
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
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayBeforeFrame : array.toNat + length.toNat * 16 ≤ frame.toNat)
    (input inputLength : BitVec 64)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4 +
      (length.toNat * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2) ≤ state.clock)
    (outerArray outerCount outerInput outerLength records outerIndex address : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBeforeFrame : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (outerBeforeArray : outerArray.toNat + outerCount.toNat * 16 ≤ array.toNat)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (addressLocal : state.locals.lookup (ofString "addr") = some (.val (.word address)))
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ (records + outerIndex * 24#64).toNat)
    (recordFits : (records + outerIndex * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessSlotSlices = (none,final)) :
    RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat := by
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
  have factor := Nat.mul_le_mul_right (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) countBound
  have tailBudget : count.toNat * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2 ≤ resumed.clock := by
    change count.toNat * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92651) + 2 ≤ bodyPost.clock
    have cost := bounded.1
    change state.clock - 1 ≤ bodyPost.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3) at cost
    apply blobHashes_budget_transfer _ _ _ state.clock bodyPost.clock (Nat.add_le_add_right factor 2) _ cost
    simpa only [← Nat.add_assoc] using budget
  have resumedIndex : resumed.locals.lookup (ofString "i") = some (.val (.word outerIndex)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "slots" ≠ ofString "i" by decide] using binding
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerValid slot inside
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have bodyOuter := rlpSlices_body_returned_outer_prefix entry bodyPost pointer length scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    heap arrayBound (by omega) heapArena entryBudget _ bodyRun outerArray outerCount outerInput outerLength entryOuter outerBeforeArray outerBeforeFrame
  have resumedOuter : RlpSliceInputPrefix resumed outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := bodyOuter slot inside
    exact ⟨p,n,item.after_frame bodyPost resumed outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have atRecords : resumed.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "slots" ≠ ofString "recs" by decide] using recordsLocal
  have atAddress : resumed.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "slots" ≠ ofString "addr" by decide] using addressLocal
  have tail := access_keys_allocation_independent_outer_prefix resumed output array count (allocationEnd array (count * 16)) input inputLength scratch frame ceiling inputLimit
    listLocal (resumedSlices.within_outer resumed array pointer length input inputLength _ starts ends) scratchPost framePost (metadata.1.trans code) resumedArena inputBound limitBound orderedFrame framePositive
    scratchBelow (Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right 16 countBound) _) arrayBeforeFrame)
    (by rw [product] at covers; exact covers.1) aligned heapPost endpoint
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 32 (Nat.le_trans countBound lengthBound)) countLimit) tailBudget
    outerArray outerCount outerInput outerLength records outerIndex address resumedOuter outerBeforeFrame
    (Nat.le_trans outerBeforeArray (by rw [product] at covers; omega)) atRecords resumedIndex atAddress outerBeforeRecord recordFits tailRun
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := tail slot inside
  exact ⟨p,n,item.after_frame output _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms access_slot_slices_independent_outer_prefix
end InitECandidate.Runtime
