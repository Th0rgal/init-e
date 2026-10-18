import InitECandidate.Runtime.AccessListSlotSlicesHeapBound
import InitECandidate.Runtime.AccessListSlotItemBound
import InitECandidate.Runtime.AccessListSlotSlicesCost
import InitECandidate.Runtime.TxListItemInputRange
import InitECandidate.Runtime.TxListItemDeclarationInputBound
import InitECandidate.Runtime.TxListItemInputNamedGlobal
import InitECandidate.Runtime.TxListItemInputGlobals
import InitECandidate.Runtime.TxListItemBlobCost
import InitECandidate.Runtime.BlobHashesDeclarationBound
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_access_slot_item_heap_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (budget : accessSlotItemCost inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state accessSlotItem
    state.clock ≤ evaluated.2.clock + accessSlotItemCost inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
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
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_tx_list_item) with
  | mk result bodyPost =>
    rw [bodyRun] at bounded
    rw [source_access_slot_item]
    refine evaluate_decCall_checked_continuation_bounded state bodyPost (ofString "sl") (ofString "tx_list_item")
      (.comb [.one,.one]) (.comb [.one,.one]) [.rfield 0 (.var .local (ofString "ent")),.const 1] [.val (.word array),.val (.word index)]
      (sourceFunctionBody Guest.guestFn_tx_list_item) _ callee result
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) (accessSlotSlicesCost inputLength.toNat)
      args lookup ?_ bodyRun bounded.2.1 ?_ bounded.2.2 ?_
    · have positive : 0 < state.clock := Nat.lt_of_lt_of_le (by unfold accessSlotItemCost; omega) budget
      exact Nat.ne_of_gt positive
    · have cost := bounded.1
      change state.clock - 1 ≤ bodyPost.clock + (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633) at cost
      exact blobHashes_call_clock_bound state.clock bodyPost.clock _ (by have base := firstBudget; change _ ≤ state.clock - 1 at base; omega) cost
    · intro value returned _
      have actual := bodyRun
      rw [returned] at actual
      obtain ⟨pointer,length,shape,starts,ends,noWrap,lengthBound⟩ := txListItem_input_returned_range entry bodyPost
        array index input inputLength filled atArray atIndex entryPrefix inside (by omega) code (by have base := firstBudget; omega) value actual
      have costBound := accessSlotSlicesCost_mono lengthBound
      have globals := txListItem_input_returned_globals entry bodyPost array index input inputLength scratch frame filled ceiling inputLimit
        atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget value actual
      have heapFrame := txListItem_input_returned_named_global entry bodyPost (ofString "heap_ptr") (by decide)
        array index input inputLength scratch frame filled ceiling inputLimit atArray atIndex entryPrefix inside inputBound limitBound
        scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget value actual
      subst value
      let resumed := setVarHOLFinite (ofString "sl") (.rStruct [.val (.word pointer),.val (.word length)]) {bodyPost with locals := state.locals}
      have atList : resumed.locals.lookup (ofString "sl") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
        simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
      have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_tx_list_item)
      rw [actual] at metadata
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
      have next := evaluate_access_slot_slices_heap_bounded resumed pointer length scratch frame heapPointer ceiling inputLimit
        atList noWrap (Nat.le_trans lengthBound inputBound) limitBound globals.1 globals.2 (metadata.1.trans code) orderedFrame framePositive
        scratchBelow resumedArena keptHeap heapBound countLimit resumedHeapArena (by omega) (Nat.le_trans ends inputBeforeHeap)
        heapAbove
        (Nat.le_trans costBound fullTailBudget)
      exact ⟨Nat.le_trans next.1 (Nat.add_le_add_left costBound _),next.2.1,next.2.2⟩

#print axioms evaluate_access_slot_item_heap_bounded
end InitECandidate.Runtime
