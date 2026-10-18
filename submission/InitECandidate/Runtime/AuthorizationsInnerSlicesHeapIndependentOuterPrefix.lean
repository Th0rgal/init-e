import InitECandidate.Runtime.RlpSlicesBodyHeapOuterPrefix
import InitECandidate.Runtime.AuthorizationsInnerSlicesIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsInnerSlicesHeapBound
import InitECandidate.Runtime.AuthorizationsEntryCheckHeapIndependentOuterPrefix
import InitECandidate.Runtime.RlpSlicesBodyOuterPrefix
import InitECandidate.Runtime.PanDecCallCheckedNormalMemoryScope
import InitECandidate.Runtime.AuthorizationsInnerSlicesSource
import InitECandidate.Runtime.AuthorizationsEntryCheckHeapBound
import InitECandidate.Runtime.RlpSlicesBodyRuntimeContract
import InitECandidate.Runtime.RlpSliceInputPrefixOuter
import InitECandidate.Runtime.OriginalRlpSlicesCode
import InitECandidate.Runtime.BlobHashesDeclarationBound
import InitECandidate.Runtime.TxScalarU256HeapInputPrefix
import InitECandidate.Runtime.TxScalarWordHeapInputPrefix
import InitECandidate.Runtime.TxFixedBytesHeapInputPrefix
import InitECandidate.Runtime.TxScalarU256HeapIndependentOuterPrefix
import InitECandidate.Runtime.TxScalarWordHeapIndependentOuterPrefix
import InitECandidate.Runtime.TxFixedBytesHeapIndependentOuterPrefix
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful inner list slicing and the complete record body preserve the earlier outer slice array. -/
theorem authorization_inner_slices_normal_heap_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (record records index pointer length input inputLength scratch frame array outerArray outerCount outerInput outerLength : BitVec 64) (ceiling inputLimit : Nat)
    (recordAddress : record = records + index * 120#64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.rfield 1 (.var .local (ofString "it")),.rfield 2 (.var .local (ofString "it"))] =
        some [.val (.word pointer),.val (.word length)])
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (inputStarts : input.toNat ≤ pointer.toNat)
    (inputEnds : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (recordBeforeArray : record.toNat + 120 ≤ array.toNat) (recordFits : record.toNat + 120 < 2^64)
    (budget : authorizationInnerSlicesCost length.toNat inputLength.toNat ≤ state.clock)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64) (outerAbove : ceiling ≤ outerArray.toNat)
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ record.toNat)
    (run : evaluateHOLFiniteState state authorizationInnerSlices = (none,final)) :
    RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat := by
  let first := length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3
  let tailCost := 6 * (inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92668)
  have total : first + 1 + tailCost ≤ state.clock := by
    simpa only [first,tailCost,authorizationInnerSlicesCost,← Nat.add_assoc] using budget
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : first ≤ entry.clock := by
    change first ≤ state.clock - 1
    exact authorization_inner_entry_budget first tailCost state.clock total
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_list_to_slices") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_list_to_slices,.comb [.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpSlices_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_list_to_slices") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) (.comb [.one,.one]) pointer length (by decide) installed
  rw [source_authorization_inner_slices] at run
  obtain ⟨value,post,ready,output,bodyRun,checked,locals,memory,globals,clock,domain,endian,readyCode,tail,restored⟩ :=
    evaluate_decCall_checked_normal_memory_scope state final (ofString "ent") (ofString "rlp_list_to_slices")
      (.comb [.one,.one]) (.comb [.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) authorizationEntryCheck callee args lookup run
  rw [bodyRun] at bounded
  have bodyCost : state.clock - 1 ≤ post.clock + first := bounded.1
  obtain ⟨count,shape,countBound,slices,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩ :=
    rlpSlices_body_returned_runtime_contract entry post pointer length scratch frame array ceiling inputLimit
      atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena heap arrayBound countLimit heapArena entryBudget inputBeforeFrame inputBeforeArray value bodyRun
  have outerEntry : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerValid slot inside
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have outerRetained := rlpSlices_body_returned_heap_outer_prefix entry post pointer length scratch frame array ceiling inputLimit
    atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow
    arena heap arrayBound countLimit heapArena entryBudget value bodyRun outerArray outerCount outerInput outerLength
    outerEntry (by omega) outerAbove
  subst value
  have outerSlices := slices.within_outer post array pointer length input inputLength count.toNat inputStarts inputEnds
  let resumed := setVarHOLFinite (ofString "ent") (.rStruct [.val (.word array),.val (.word count)]) ready
  have resumedPrefix : RlpSliceInputPrefix resumed array input inputLength count.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerSlices slot inside
    exact ⟨p,n,item.after_frame post resumed array slot p n input inputLength domain (congrFun memory _) (congrFun memory _)⟩
  have resumedOuter : RlpSliceInputPrefix resumed outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerRetained slot inside
    exact ⟨p,n,item.after_frame post resumed outerArray slot p n outerInput outerLength domain (congrFun memory _) (congrFun memory _)⟩
  have atEntry : resumed.locals.lookup (ofString "ent") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atRecords : resumed.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "ent" ≠ ofString "recs" by decide] using recordsLocal
  have atIndex : resumed.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "ent" ≠ ofString "i" by decide] using indexLocal
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [bodyRun] at metadata
  have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [domain,metadata.2.1]
    exact arena address lower upper
  have tailBudget : tailCost ≤ resumed.clock := by
    change tailCost ≤ ready.clock
    rw [clock]
    exact blobHashes_budget_transfer first tailCost tailCost state.clock post.clock (Nat.le_refl _) total bodyCost
  have retained := authorization_entry_check_normal_heap_independent_outer_prefix resumed output record records index array count input inputLength scratch frame
    outerArray outerCount outerInput outerLength ceiling inputLimit recordAddress atRecords atIndex (Or.inr recordBeforeArray) recordFits atEntry resumedPrefix inputBound
    limitBound (by simpa only [resumed,setVarHOLFinite,globals] using scratchPost)
    (by simpa only [resumed,setVarHOLFinite,globals] using framePost)
    (by change ready.code = originalRuntimeCode; exact readyCode.trans (metadata.1.trans code))
    orderedFrame framePositive scratchBelow resumedArena
    (interval.trans (by decide)) arrayAbove tailBudget
    resumedOuter outerFits outerAbove outerBeforeRecord tail
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := retained slot inside
  exact ⟨p,n,item.after_frame output _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms authorization_inner_slices_normal_heap_independent_outer_prefix
end InitECandidate.Runtime
