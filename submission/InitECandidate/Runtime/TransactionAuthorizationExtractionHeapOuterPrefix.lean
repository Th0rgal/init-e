import InitECandidate.Runtime.TransactionAuthorizationExtractionOuterPrefix
import InitECandidate.Runtime.TxListItemIndependentOuterPrefix
import InitECandidate.Runtime.TransactionAuthorizationExtractionHeapBound
import InitECandidate.Runtime.TransactionAuthorizationDecodeHeapOuterPrefix
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxListItemHeapInputPrefix
import InitECandidate.Runtime.TxListItemHeapIndependentOuterPrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_authorization_extraction_normal_heap_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (array count index tx input inputLength scratch frame heapPointer : BitVec 64) (ceiling inputLimit : Nat)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "k") = some (.val (.word index)))
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat) (inside : index.toNat < count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeHeap : input.toNat + inputLength.toNat ≤ heapPointer.toNat)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (heapAbove : ceiling ≤ heapPointer.toNat)
    (arrayFits : array.toNat + count.toNat * 16 ≤ 2^64) (arrayAbove : ceiling ≤ array.toNat)
    (arrayBeforeHeap : array.toNat + count.toNat * 16 ≤ heapPointer.toNat)
    (headerBefore : tx.toNat + 280 < array.toNat)
    (watchedArray watchedCount watchedInput watchedLength : BitVec 64)
    (watchedValid : RlpSliceInputPrefix state watchedArray watchedInput watchedLength watchedCount.toNat)
    (watchedFits : watchedArray.toNat + watchedCount.toNat * 16 ≤ 2^64) (watchedAbove : ceiling ≤ watchedArray.toNat)
    (watchedBeforeHeap : watchedArray.toNat + watchedCount.toNat * 16 ≤ heapPointer.toNat)
    (watchedBeforeTx : watchedArray.toNat + watchedCount.toNat * 16 ≤ tx.toNat)
    (heapAligned : heapPointer.toNat % 8 = 0)
    (budget : txListItemAuthorizationCost inputLength.toNat ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionAuthorizationExtraction = (none,final)) :
    RlpSliceInputPrefix final watchedArray watchedInput watchedLength watchedCount.toNat := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "arr"),.var .local (ofString "k")] = some [.val (.word array),.val (.word index)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,arrayLocal,indexLocal]
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "arr",.val (.word array))).update (ofString "i",.val (.word index))
  let entry := callEntryStateHOLFinite state callee
  have atArray : entry.locals.lookup (ofString "arr") = some (.val (.word array)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "arr" by decide]
  have atIndex : entry.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryPrefix : RlpSliceInputPrefix entry array input inputLength count.toNat := by
    intro slot bounded
    obtain ⟨p,n,item⟩ := valid slot bounded
    exact ⟨p,n,RlpSliceInputEntry.after_frame state entry array slot p n input inputLength item rfl rfl rfl⟩
  have firstBudget : inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ entry.clock := by
    change inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92633 ≤ state.clock - 1
    have base := Nat.le_trans (Nat.le_add_right
      (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92634) (authorizationBodyCost inputLength.toNat + 1)) budget
    omega
  have bounded := evaluate_txListItem_input_bounded entry array index input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget
  have installed : state.code.lookup (ofString "tx_list_item") =
      some ([(ofString "arr",.one),(ofString "i",.one)],sourceFunctionBody Guest.guestFn_tx_list_item,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_txListItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "tx_list_item") (ofString "arr") (ofString "i")
    (sourceFunctionBody Guest.guestFn_tx_list_item) (.comb [.one,.one]) array index (by decide) installed
  rw [source_transaction_authorization_extraction] at run
  obtain ⟨value,bodyPost,output,bodyRun,checked,tailRun,restored⟩ := evaluate_decCall_checked_normal_exact_scope state final
    (ofString "aul") (ofString "tx_list_item") (.comb [.one,.one]) (.comb [.one,.one]) _ _
    (sourceFunctionBody Guest.guestFn_tx_list_item) transactionAuthorizationDecode callee args lookup run
  rw [bodyRun] at bounded
  obtain ⟨pointer,length,shape,starts,ends,noWrap,lengthBound⟩ := txListItem_input_returned_range entry bodyPost
    array index input inputLength count.toNat atArray atIndex entryPrefix inside (by omega) code (by have base := firstBudget; omega) value bodyRun
  have globals := txListItem_input_returned_globals entry bodyPost array index input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget value bodyRun
  have heapFrame := txListItem_input_returned_named_global entry bodyPost (ofString "heap_ptr") (by decide)
    array index input inputLength scratch frame count.toNat ceiling inputLimit atArray atIndex entryPrefix inside inputBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget value bodyRun
  subst value
  let resumed := setVarHOLFinite (ofString "aul") (.rStruct [.val (.word pointer),.val (.word length)]) {bodyPost with locals := state.locals}
  have atList : resumed.locals.lookup (ofString "aul") = some (.rStruct [.val (.word pointer),.val (.word length)]) := by
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
  have fullTailBudget : authorizationBodyCost inputLength.toNat + 1 ≤ resumed.clock := by
    change authorizationBodyCost inputLength.toNat + 1 ≤ bodyPost.clock
    apply blobHashes_budget_transfer _ _ _ state.clock bodyPost.clock (Nat.le_refl _) _ bounded.1
    simpa only [txListItemAuthorizationCost,← Nat.add_assoc] using budget
  have keptHeap : resumed.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)) := heapFrame.trans heap
  have entryWatched : RlpSliceInputPrefix entry watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := watchedValid slot within
    exact ⟨p,n,item.after_frame state entry watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have bodyPrefix := txListItem_input_returned_heap_independent_outer_prefix entry bodyPost array index input inputLength scratch frame count.toNat ceiling inputLimit
    atArray atIndex entryPrefix inside inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget _ bodyRun
    watchedArray watchedCount watchedInput watchedLength entryWatched watchedFits watchedAbove
  have resumedPrefix : RlpSliceInputPrefix resumed watchedArray watchedInput watchedLength watchedCount.toNat := by
    intro slot within
    obtain ⟨p,n,item⟩ := bodyPrefix slot within
    exact ⟨p,n,item.after_frame bodyPost resumed watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩
  have atTx : resumed.locals.lookup (ofString "tx") = some (.val (.word tx)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "aul" ≠ ofString "tx" by decide] using txLocal
  have next := transaction_authorization_decode_normal_heap_outer_prefix resumed output pointer length input inputLength scratch frame heapPointer ceiling inputLimit
    atList noWrap (Nat.le_trans lengthBound inputBound) inputBound starts ends (by omega) inputBeforeHeap limitBound globals.1 globals.2
    (metadata.1.trans code) orderedFrame framePositive scratchBelow resumedArena keptHeap heapBound countLimit resumedHeapArena
    (by omega) (Nat.le_trans ends inputBeforeHeap) heapAbove heapAligned fullTailBudget
    watchedArray watchedCount watchedInput watchedLength resumedPrefix watchedFits watchedAbove watchedBeforeHeap tx atTx watchedBeforeTx
    (by have bound := array.isLt; omega) tailRun
  rw [restored]
  intro slot within
  obtain ⟨p,n,item⟩ := next slot within
  exact ⟨p,n,item.after_frame output _ watchedArray slot p n watchedInput watchedLength rfl rfl rfl⟩

#print axioms transaction_authorization_extraction_normal_heap_outer_prefix
end InitECandidate.Runtime
