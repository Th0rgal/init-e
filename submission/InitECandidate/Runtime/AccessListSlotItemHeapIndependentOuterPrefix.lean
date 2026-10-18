import InitECandidate.Runtime.AccessListSlotItemOuterPrefix
import InitECandidate.Runtime.TxListItemHeapIndependentOuterPrefix
import InitECandidate.Runtime.AccessListSlotItemBound
import InitECandidate.Runtime.AccessListSlotSlicesHeapIndependentOuterPrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem access_slot_item_heap_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array index input inputLength scratch frame heapPointer : BitVec 64) (filled ceiling inputLimit : Nat)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [.rfield 0 (.var .local (ofString "ent")),.const 1] =
      some [.val (.word array),.val (.word index)])
    (valid : RlpSliceInputPrefix state array input inputLength filled) (inside : index.toNat < filled)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 32 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (budget : accessSlotItemCost inputLength.toNat ≤ state.clock)
    (outerArray outerCount outerInput outerLength records outerIndex address : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerAbove : ceiling ≤ outerArray.toNat)
    (outerBeforeHeap : outerArray.toNat + outerCount.toNat * 16 ≤ heapPointer.toNat)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (binding : state.locals.lookup (ofString "i") = some (.val (.word outerIndex)))
    (addressLocal : state.locals.lookup (ofString "addr") = some (.val (.word address)))
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ (records + outerIndex * 24#64).toNat)
    (recordFits : (records + outerIndex * 24#64).toNat + 24 < 2^64)
    (run : evaluateHOLFiniteState state accessSlotItem = (none,final)) :
    RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength filled := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have firstBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    have base := Nat.le_trans (Nat.le_add_right
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) (accessSlotSlicesCost inputLength.toNat)) budget
    omega
  have bounded := evaluate_txListItem_input_bounded entry array index input inputLength scratch frame filled ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget
  have installed : state.code.lookup (ofString "tx_list_item") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_list_item,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_txListItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_list_item") (ofString "arr") (ofString "i")
    (sourceFunctionBody Guest.guestFn_tx_list_item) (.comb [.one,.one]) array index (by decide) installed
  rw [source_access_slot_item] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "sl") (ofString "tx_list_item") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_tx_list_item) accessSlotSlices callee args lookup run
  rw [bodyRun] at bounded
  obtain ⟨pointer,length,shape,starts,ends,noWrap,lengthBound⟩ := txListItem_input_returned_range entry bodyPost
    array index input inputLength filled atArray atIndex entryPrefix inside (by omega) code (by have base := firstBudget; omega) value bodyRun
  have globals := txListItem_input_returned_globals entry bodyPost array index input inputLength scratch frame filled ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget value bodyRun
  have heapFrame := txListItem_input_returned_named_global entry bodyPost (ofString "heap_ptr") (by decide)
    array index input inputLength scratch frame filled ceiling inputLimit atArray atIndex entryPrefix inside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget value bodyRun
  subst value
  let resumed := setVarHOLFinite (ofString "sl") (.rStruct [.val (.word pointer),.val (.word length)]) {bodyPost with locals := state.locals}
  have atList : resumed.locals.lookup (ofString "sl") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_list_item)
  rw [bodyRun] at metadata
  have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
    intro address lower upper
    change bodyPost.memaddrs address
    rw [metadata.2.1]
    exact arena address lower upper
  have resumedHeapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → resumed.memaddrs address := by
    intro address lower upper
    change bodyPost.memaddrs address
    rw [metadata.2.1]
    exact heapArena address lower upper
  have fullTailBudget : accessSlotSlicesCost inputLength.toNat ≤ resumed.clock := by
    change accessSlotSlicesCost inputLength.toNat ≤ bodyPost.clock
    apply blobHashes_budget_transfer _ _ _ state.clock bodyPost.clock (Nat.le_refl _) _ bounded.1
    simpa only [accessSlotItemCost,← Nat.add_assoc] using budget
  have keptHeap : resumed.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)) := heapFrame.trans heap
  have resumedIndex : resumed.locals.lookup (ofString "i") = some (.val (.word outerIndex)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "sl" ≠ ofString "i" by decide] using binding
  have entryOuter : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerValid slot inside
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have bodyOuter := txListItem_input_returned_heap_independent_outer_prefix entry bodyPost array index input inputLength scratch frame filled ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    firstBudget _ bodyRun outerArray outerCount outerInput outerLength entryOuter (by have top := heapPointer.isLt; omega) outerAbove
  have resumedOuter : RlpSliceInputPrefix resumed outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := bodyOuter slot inside
    exact ⟨p,n,item.after_frame bodyPost resumed outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have atRecords : resumed.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "sl" ≠ ofString "recs" by decide] using recordsLocal
  have atAddress : resumed.locals.lookup (ofString "addr") = some (.val (.word address)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "sl" ≠ ofString "addr" by decide] using addressLocal
  have next := access_slot_slices_heap_independent_outer_prefix resumed output pointer length scratch frame heapPointer ceiling inputLimit
    atList noWrap (Nat.le_trans lengthBound inputBound) limitBound globals.1 globals.2 (metadata.1.trans code) orderedFrame framePositive
    scratchBelow resumedArena keptHeap heapBound countLimit resumedHeapArena (by omega) (Nat.le_trans ends inputBeforeHeap)
    input inputLength inputBound starts ends (Nat.le_trans (access_slot_slices_mixed_cost_le lengthBound) fullTailBudget)
    outerArray outerCount outerInput outerLength records outerIndex address resumedOuter outerAbove outerBeforeHeap atRecords resumedIndex atAddress
    outerBeforeRecord recordFits tailRun
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := next slot inside
  exact ⟨p,n,item.after_frame output _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms access_slot_item_heap_independent_outer_prefix
end InitECandidate.Runtime
