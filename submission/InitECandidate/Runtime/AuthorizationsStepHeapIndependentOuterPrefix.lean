import InitECandidate.Runtime.RlpItemBodyAbove
import InitECandidate.Runtime.RlpSliceInputPrefixAbove
import InitECandidate.Runtime.AuthorizationsStepIndependentOuterPrefix
import InitECandidate.Runtime.AuthorizationsStepHeapBound
import InitECandidate.Runtime.AuthorizationsItemCheckHeapIndependentOuterPrefix
import InitECandidate.Runtime.RlpItemBodyBelow
import InitECandidate.Runtime.PanDecCallCheckedNormalMemoryScope
import InitECandidate.Runtime.AuthorizationsStepSource
import InitECandidate.Runtime.AuthorizationsItemCheckHeapBound
import InitECandidate.Runtime.AuthorizationsInnerCostMonotone
import InitECandidate.Runtime.RlpItemBodyRuntimeContract
import InitECandidate.Runtime.RlpItemBodyBound
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

/-- The actual authorization-loop iteration includes item parsing, both guards,
inner list slicing, all record fields, stores and index increment. -/
theorem authorization_step_normal_heap_independent_outer_prefix {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (record records index pointer length input inputLength scratch frame array outerArray outerCount outerInput outerLength : BitVec 64) (ceiling inputLimit : Nat)
    (recordAddress : record = records + index * 120#64)
    (recordsLocal : state.locals.lookup (ofString "recs") = some (.val (.word records)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) authorizationStepArguments =
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
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (recordBeforeArray : record.toNat + 120 ≤ array.toNat) (recordFits : record.toNat + 120 < 2^64)
    (budget : authorizationStepCost length.toNat inputLength.toNat ≤ state.clock)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerFits : outerArray.toNat + outerCount.toNat * 16 ≤ 2^64) (outerAbove : ceiling ≤ outerArray.toNat)
    (outerBeforeRecord : outerArray.toNat + outerCount.toNat * 16 ≤ record.toNat)
    (run : evaluateHOLFiniteState state authorizationStep = (none,final)) :
    RlpSliceInputPrefix final outerArray outerInput outerLength outerCount.toNat := by
  let first := length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632
  let tailCost := authorizationInnerSlicesCost inputLength.toNat inputLength.toNat
  have totalBudget : first + 1 + tailCost ≤ state.clock := by
    simpa only [first,tailCost,authorizationStepCost,← Nat.add_assoc] using budget
  let callee := rlpHeaderCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : first ≤ entry.clock := by
    change first ≤ state.clock - 1
    exact authorization_inner_entry_budget first tailCost state.clock totalBudget
  have bounded := evaluate_rlpItem_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  have installed : state.code.lookup (ofString "rlp_item") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
  rw [source_authorization_step] at run
  obtain ⟨value,post,ready,output,bodyRun,checked,locals,memory,globals,clock,domain,endian,readyCode,tail,restored⟩ :=
    evaluate_decCall_checked_normal_memory_scope state final (ofString "it") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_rlp_item) authorizationItemCheck callee args lookup run
  rw [bodyRun] at bounded
  have bodyCost : state.clock - 1 ≤ post.clock + first := bounded.1
  have outerEntry : RlpSliceInputPrefix entry outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerValid slot inside
    exact ⟨p,n,item.after_frame state entry outerArray slot p n outerInput outerLength rfl rfl rfl⟩
  have metadataBefore := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadataBefore
  have outerRetained : RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
    apply outerEntry.after_memory_above entry post outerArray outerCount outerInput outerLength outerFits metadataBefore.2.1
    intro address aboveOuter
    exact rlpItem_body_returned_above entry post pointer length scratch frame ceiling inputLimit atPointer atLength noWrap lengthBound
      limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget _ bodyRun address (by omega)
  obtain ⟨kind,payloadPointer,payload,consumed,shape,starts,ends,payloadNoWrap,payloadBound,scratchPost,framePost,heapSame⟩ :=
    rlpItem_body_returned_runtime_contract entry post pointer length scratch frame ceiling inputLimit atPointer atLength
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget value bodyRun
  subst value
  let resumed := setVarHOLFinite (ofString "it")
    (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) ready
  have atItem : resumed.locals.lookup (ofString "it") =
      some (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atRecords : resumed.locals.lookup (ofString "recs") = some (.val (.word records)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "it" ≠ ofString "recs" by decide] using recordsLocal
  have atIndex : resumed.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "it" ≠ ofString "i" by decide] using indexLocal
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadata
  have resumedArena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → resumed.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [domain,metadata.2.1]
    exact arena address lower upper
  have resumedHeapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → resumed.memaddrs address := by
    intro address lower upper
    change ready.memaddrs address
    rw [domain,metadata.2.1]
    exact heapArena address lower upper
  have tailBudget : tailCost ≤ resumed.clock := by
    change tailCost ≤ ready.clock
    rw [clock]
    exact blobHashes_budget_transfer first tailCost tailCost state.clock post.clock (Nat.le_refl _) totalBudget bodyCost
  have insideInput : payload.toNat ≤ inputLength.toNat := by omega
  have costBound := authorizationInnerSlicesCost_mono_left payload.toNat inputLength.toNat inputLength.toNat insideInput
  have resumedOuter : RlpSliceInputPrefix resumed outerArray outerInput outerLength outerCount.toNat := by
    intro slot inside
    obtain ⟨p,n,item⟩ := outerRetained slot inside
    exact ⟨p,n,item.after_frame post resumed outerArray slot p n outerInput outerLength domain (congrFun memory _) (congrFun memory _)⟩
  have next := authorization_item_check_normal_heap_independent_outer_prefix resumed output record records index kind payloadPointer payload consumed
    input inputLength scratch frame array outerArray outerCount outerInput outerLength ceiling inputLimit recordAddress atRecords atIndex atItem payloadNoWrap
    (Nat.le_trans payloadBound lengthBound) inputBound limitBound (Nat.le_trans inputStarts starts) (Nat.le_trans ends inputEnds)
    (by simpa only [resumed,setVarHOLFinite,globals] using scratchPost)
    (by simpa only [resumed,setVarHOLFinite,globals] using framePost)
    (by change ready.code = originalRuntimeCode; exact readyCode.trans (metadata.1.trans code)) orderedFrame framePositive scratchBelow resumedArena (by simpa only [resumed,setVarHOLFinite,globals] using heapSame.trans heap)
    arrayBound countLimit resumedHeapArena (by omega) (Nat.le_trans ends inputBeforeArray)
    arrayAbove
    recordBeforeArray recordFits (Nat.le_trans costBound tailBudget)
    resumedOuter outerFits outerAbove outerBeforeRecord tail
  rw [restored]
  intro slot inside
  obtain ⟨p,n,item⟩ := next slot inside
  exact ⟨p,n,item.after_frame output _ outerArray slot p n outerInput outerLength rfl rfl rfl⟩

#print axioms authorization_step_normal_heap_independent_outer_prefix
end InitECandidate.Runtime
