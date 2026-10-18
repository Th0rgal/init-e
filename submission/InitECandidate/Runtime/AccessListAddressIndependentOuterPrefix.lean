import InitECandidate.Runtime.TxFixedBytesIndependentOuterPrefix
import InitECandidate.Runtime.AccessListAddressBound
import InitECandidate.Runtime.AccessListSlotItemIndependentOuterPrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_address_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (entryLocal : state.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : 1 < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (arrayBelowFrame : array.toNat + count.toNat * 16 ≤ frame.toNat)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (heapBeforeFrame : heapPointer.toNat + inputLength.toNat * 16 ≤ frame.toNat)
    (budget : (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) + accessSlotItemCost inputLength.toNat ≤ state.clock)
    (outerArray outerCount outerInput outerLength records outerIndex : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBeforeFrame : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (outerBeforeHeap : outerArray.toNat + outerCount.toNat * 16 ≤ heapPointer.toNat)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ (records + outerIndex * 24#64).toNat)
    (recordFits : (records + outerIndex * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessAddress = (none,final)) :
    RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat := by
  let cost := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := ((HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update
    (ofString "i",.val (.word (0 : BitVec 64)))).update (ofString "width",.val (.word (20 : BitVec 64)))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "arr" by decide,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "width" ≠ ofString "i" by decide]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := valid slot inside
    exact ⟨p,n,item.after_frame state entry array slot p n input inputLength rfl rfl rfl⟩
  have inside1 : (0 : BitVec 64).toNat < count.toNat := by change 0 < count.toNat; omega
  have bodyBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    omega
  have bounded := evaluate_txFixedBytes_input_bounded entry array 0 input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena bodyBudget
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 0,.const 20] =
      some [.val (.word array),.val (.word (0 : BitVec 64)),.val (.word (20 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,entryLocal]
  have installed := originalRuntimeCode_txFixedBytes_lookup
  rw [← code] at installed
  have lookup := pan_three_word_lookup state.code.lookup (ofString "tx_fixed_bytes")
    (ofString "arr") (ofString "i") (ofString "width") (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
    array 0 20 (by decide) (by decide) (by decide) installed
  rw [source_access_address] at run
  obtain ⟨value,post,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "addr") (ofString "tx_fixed_bytes") .one .one _ _
    (sourceFunctionBody Guest.guestFn_tx_fixed_bytes) accessSlotItem callee args lookup run
  have wordShape : ∃ word : BitVec 64, value = .val (.word word) := by
    have goodShape := checked.1
    cases value with
    | val atom => cases atom with | word word => exact ⟨word,rfl⟩
    | rStruct fields => simp [shapeOfHOLExact,shapeEqHOL] at goodShape
    | nStruct name fields => simp [shapeOfHOLExact,shapeEqHOL] at goodShape
  obtain ⟨address,rfl⟩ := wordShape
  rw [bodyRun] at bounded
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_fixed_bytes)
  rw [bodyRun] at metadata
  have tailBudget : accessSlotItemCost inputLength.toNat ≤ post.clock := by
    have spent := bounded.1
    change state.clock - 1 ≤ post.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633) at spent
    omega
  have retainedPrefix := txFixedBytes_input_returned_prefix entry post array 0 input inputLength scratch frame count ceiling inputLimit
    atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
    arena bodyBudget (.val (.word address)) bodyRun arrayBelowFrame
  have globals := txFixedBytes_input_returned_global_frame entry post array 0 input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
    arena bodyBudget (.val (.word address)) bodyRun
  let resumed := setVarHOLFinite (ofString "addr") (.val (.word address)) {post with locals := state.locals}
  have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := retainedPrefix slot within
    exact ⟨p,n,item.after_frame post resumed array slot p n input inputLength rfl rfl rfl⟩
  have atEntry : resumed.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "addr" ≠ ofString "ent" by decide] using entryLocal
  have nextArgs : evalListHOLFinite resumed (h := fun a => Classical.propDecidable (resumed.memaddrs a))
      [.rfield 0 (.var .local (ofString "ent")),.const 1] = some [.val (.word array),.val (.word (1 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atEntry]
  have resumedIndex : resumed.locals.lookup (ofString "i") = some (.val (.word outerIndex)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "addr" ≠ ofString "i" by decide] using binding
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := outerValid slot within
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have bodyOuter := txFixedBytes_input_returned_independent_outer_prefix entry post array 0 input inputLength scratch frame count ceiling inputLimit
    atArray atIndex entryPrefix inside1 inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    bodyBudget (.val (.word address)) bodyRun outerArray outerCount outerInput outerLength entryOuter outerBeforeFrame
  have resumedOuter : RlpSliceInputPrefix resumed outerArray outerInput outerLength outerCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := bodyOuter slot within
    exact ⟨p,n,item.after_frame post resumed outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have atRecords : resumed.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "addr" ≠ ofString "recs" by decide] using recordsLocal
  have atAddress : resumed.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have next := access_slot_item_independent_outer_prefix resumed output array 1 input inputLength scratch frame heapPointer count.toNat ceiling inputLimit
    nextArgs resumedPrefix (by simpa using inside) inputBound limitBound ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal)
    (metadata.1.trans code) orderedFrame framePositive scratchBelow
    (by intro address lower upper; change post.memaddrs address; rw [metadata.2.1]; exact arena address lower upper)
    ((globals _).trans heap) heapBound countLimit
    (by intro address lower upper; change post.memaddrs address; rw [metadata.2.1]; exact heapArena address lower upper)
    inputBeforeHeap heapBeforeFrame tailBudget outerArray outerCount outerInput outerLength records outerIndex address resumedOuter outerBeforeFrame outerBeforeHeap
    atRecords resumedIndex atAddress outerBeforeRecord recordFits tailRun
  rw [restored]
  intro slot within
  obtain ⟨p,n,item⟩ := next slot within
  exact ⟨p,n,item.after_frame output _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms access_address_independent_outer_prefix
end InitECandidate.Runtime
