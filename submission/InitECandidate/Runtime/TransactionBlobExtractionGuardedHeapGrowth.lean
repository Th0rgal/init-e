import InitECandidate.Runtime.BlobHashesCostMonotone
import InitECandidate.Runtime.TxListItemInputPrefix
import InitECandidate.Runtime.TransactionBlobExtractionBound
import InitECandidate.Runtime.TransactionBlobDecodeGuardedHeapGrowth
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_blob_extraction_normal_guarded_heap_growth {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count index input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : (index + 1).toNat < count.toNat)
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
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (budget : txListItemBlobCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionBlobExtraction = (none,final)) :
    ∃ nextHeap : BitVec 64,
      final.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      heapPointer.toNat ≤ nextHeap.toNat ∧ nextHeap.toNat ≤ heapPointer.toNat + inputLength.toNat * 48 ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      final.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      final.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.op .add [.var .local (ofString "k"),.const 1]] = some [.val (.word array),.val (.word (index + 1))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word (index + 1)))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word (index + 1))) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have firstBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    have base := Nat.le_trans (Nat.le_add_right
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) (blobHashesBodyCost inputLength.toNat + 1)) budget
    omega
  have bounded := evaluate_txListItem_input_bounded entry array (index + 1) input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget
  have installed : state.code.lookup (ofString "tx_list_item") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_list_item,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_txListItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_list_item") (ofString "arr") (ofString "i")
    (sourceFunctionBody Guest.guestFn_tx_list_item) (.comb [.one,.one]) array (index + 1) (by decide) installed
  rw [source_transaction_blob_extraction] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "bl") (ofString "tx_list_item") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_tx_list_item) transactionBlobDecode callee args lookup run
  rw [bodyRun] at bounded
  obtain ⟨pointer,length,shape,starts,ends,noWrap,lengthBound⟩ := txListItem_input_returned_range entry bodyPost
    array (index + 1) input inputLength count.toNat atArray atIndex entryPrefix inside (by omega) code (by have base := firstBudget; omega) value bodyRun
  have globals := txListItem_input_returned_globals entry bodyPost array (index + 1) input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget value bodyRun
  have heapFrame := txListItem_input_returned_named_global entry bodyPost (ofString "heap_ptr") (by decide)
    array (index + 1) input inputLength scratch frame count.toNat ceiling inputLimit atArray atIndex entryPrefix inside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget value bodyRun
  subst value
  let resumed := setVarHOLFinite (ofString "bl") (.rStruct [.val (.word pointer),.val (.word length)]) {bodyPost with locals := state.locals}
  have atList : resumed.locals.lookup (ofString "bl") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
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
  have fullTailBudget : blobHashesBodyCost inputLength.toNat + 1 ≤ resumed.clock := by
    change blobHashesBodyCost inputLength.toNat + 1 ≤ bodyPost.clock
    apply blobHashes_budget_transfer _ _ _ state.clock bodyPost.clock (Nat.le_refl _) _ bounded.1
    simpa only [txListItemBlobCost,← Nat.add_assoc] using budget
  have keptHeap : resumed.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)) := heapFrame.trans heap
  have costBound := blobHashesBodyCost_mono lengthBound
  obtain ⟨nextHeap,binding,floor,growth,heapLimit,aligned,scratchFinal,frameFinal⟩ := transaction_blob_decode_normal_guarded_heap_growth resumed output
    pointer length scratch frame heapPointer ceiling inputLimit atList noWrap (Nat.le_trans lengthBound inputBound) limitBound globals.1 globals.2
    (metadata.1.trans code) orderedFrame framePositive scratchBelow resumedArena keptHeap heapBound countLimit resumedHeapArena
    (by omega) (Nat.le_trans ends inputBeforeHeap)
    heapAbove heapAligned
    (Nat.le_trans (Nat.add_le_add_right costBound 1) fullTailBudget) tailRun
  have bytes := Nat.mul_le_mul_right 48 lengthBound
  rw [restored]
  exact ⟨nextHeap,binding,floor,by omega,heapLimit,aligned,scratchFinal,frameFinal⟩

#print axioms transaction_blob_extraction_normal_guarded_heap_growth
end InitECandidate.Runtime
